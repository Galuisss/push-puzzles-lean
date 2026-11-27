/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportSecond
public import Push.AcceptanceSoundnessSupportGuardBarrier
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgram
import all Push.Scan
import all PushS.PortCentralStrip
import all PushS.PortStreetSupport
import all PushS.PortSegments

/-! The first real endpoint support uses the retained guard marker to exclude the temporary private-neighbor row. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem trim_touch_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (trimRound l p side) q) :
    q.1.val ∈ streetColumns l (coordinates p) := by
  obtain ⟨request, hr, hx⟩ := ht
  obtain ⟨a, ha', he⟩ := List.mem_map.mp hr
  have hstreet := acceptance_column_street l p hl hM ha side (List.mem_filter.mp ha').1
  have hcol : q.1.val = a.column := by cases side <;> simpa only [← he, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
  exact hcol.symm ▸ hstreet

private theorem main_touch_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (mainRound l p side) q) :
    q.1.val ∈ streetColumns l (coordinates p) := by
  obtain ⟨request, hr, hx⟩ := ht
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hr
  have hstreet := axis_in_streetColumns l p (l.endpoints_port_lt hl (List.mem_filter.mp he).1)
  have hcol : q.1.val = p.x e.port := by cases side <;> simpa only [← heq, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
  exact hcol.symm ▸ hstreet

private theorem private_touch_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (privateRound l p) q) :
    q.1.val ∈ streetColumns l (coordinates p) := by
  have hx := prefix_touches p .south (privateColumns l p) _ ht
  obtain ⟨a, ha', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  change a.column = q.1.val at he
  exact he ▸ acceptance_column_street l p hl hM ha .lower (List.mem_filter.mp ha').1

private theorem axes_street (l : PortLayout) (p : Scales.Parameters) {x : ℕ} (hx : x ∈ axes l p) :
    x ∈ streetColumns l (coordinates p) := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact he ▸ axis_in_streetColumns l p (List.mem_range.mp hi)

private theorem axis_touch_street (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (axisReadRound l p) q) :
    q.1.val ∈ streetColumns l (coordinates p) := by
  obtain ⟨a, ha, hx⟩ := ht
  change q.1.val = a.1 at hx
  rcases List.mem_append.mp ha with ha | ha
  · exact hx.symm ▸ axes_street l p (Finset.mem_sdiff.mp ((mem_prefixRequests _ _ _ _).mp ha).1).1
  · exact hx.symm ▸ axes_street l p (l.acceptanceCore_subset_axes p hl ((mem_prefixRequests _ _ _ _).mp ha).1)

private theorem probe_rows_work (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {y : ℕ} (hy : y ∈ probeRows l p) : y ∈ workRows l p := by
  obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hy)
  have hj := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  exact heq ▸ (level_work_rows l p .upper hj.1 hj.2).2

private theorem frame_first (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hf : q ∈ Boundary.frame) : q ∈ (supportCoordinates l p).first := by
  apply (first_support_iff l p q).mpr
  rcases frame_onStreet l p hf with hx | hy
  · exact Or.inl hx
  · exact Or.inr (Finset.mem_union_left _ (List.mem_toFinset.mpr hy))

set_option maxHeartbeats 400000 in
/-- Every actual accepted endpoint, with only its new markers filled, lies on F(X,Y∪Z). -/
theorem program_first_supported (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (supportCoordinates l p).first (Blocked.fill t (newCentralMarkers l p)) := by
  intro q hq
  have hholes : q ∈ PushS.holes t := (PushS.mem_holes _).mpr (fun hb => hq (Finset.mem_union_left _ hb))
  have hnew : q ∉ newCentralMarkers l p := fun hm => hq (Finset.mem_union_right _ hm)
  by_contra hout
  have hframe : q ∉ Boundary.frame := fun hf => hout (frame_first l p hf)
  have hrows : q.2.val ∉ newMarkerRows p := by
    intro hy
    exact hnew (program_new_rows_stock l p hl hM haxes initial target hr hp hs ha hholes hframe hy)
  have hcol : q.1.val ∉ streetColumns l (coordinates p) := fun hx => hout ((first_support_iff l p q).mpr (Or.inl hx))
  have hwork : q.2.val ∉ workRows l p := fun hy => hout ((first_support_iff l p q).mpr (Or.inr (Finset.mem_union_left _ hy)))
  have hcut : q.2.val ∉ cutRows p := fun hy => hout ((first_support_iff l p q).mpr (Or.inr (Finset.mem_union_right _ hy)))
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let E := PushS.holes t
  have hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E :=
    (program_clean_execution l p hl hM haxes initial target hr hs ha).2
  have htake8 : stages.take 8 = mainAxisSchedule l p (T \ Boundary.frame).card := by
    simp only [stages, schedule, preparation, frameSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule,
      firstRowKeep, mainRound, mainTop, mainBottom, List.cons_append, List.nil_append, List.take_succ_cons,
      List.take_zero, reduceCtorEq, ite_true, ite_false]
  have hq8 : q ∈ roundResidual stages T E 8 := by
    apply clean_unread_survives (stages.take 8) T E _ (roundResidual_clean stages T E 8 hc)
      (roundResidual_eval stages T E 8 hc) hholes
    intro stage hstage ht
    rw [htake8] at hstage
    simp only [mainAxisSchedule, firstRowSchedule, firstTrimSchedule, frameSchedule,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hstage
    rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨a, ha', hx⟩ := ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact hframe ((Boundary.mem_frame q).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩)
      · exact hframe ((Boundary.mem_frame q).mpr ⟨.east, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change q.1.val = p.W at hx; omega⟩⟩)
    · obtain ⟨a, ha', hx⟩ := ht
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
      rcases ha' with rfl | rfl
      · exact hframe ((Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx⟩⟩)
      · exact hframe ((Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by change q.2.val = p.H at hx; omega⟩⟩)
    · exact ht
    · exact hcol (trim_touch_street l p hl hM haxes .lower ht)
    · exact hcol (trim_touch_street l p hl hM haxes .upper ht)
    · exact ht
    · exact hcol (main_touch_street l p hl .upper ht)
    · exact hcol (main_touch_street l p hl .lower ht)
  have i8 : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have h8 := roundResidual_clear_keeps stages T E 8 hc i8 hq8
  have hbridge : q.2.val = p.H - p.Y 1 - 1 := by
    have hret : q.2.val ∈ secondRowKeep l p := by
      by_contra hn
      exact h8.2 (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, hn⟩)
    simp only [secondRowKeep, keepRows, Finset.mem_union, Finset.mem_singleton] at hret
    exact hret.resolve_left (fun h => h.elim (fun h => h.elim hwork hcut) hrows)
  have i9 : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq10 := roundResidual_unread_keeps stages T E 9 hc i9 h8.1 (fun ht => hcol (private_touch_street l p hl hM haxes ht))
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have hy := row_touches p .east _ (Or.inr rfl) ht
    apply hrows
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    exact hy.elim Or.inl (fun he => Or.inr (Or.inl he)))
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 : q ∈ roundResidual stages T E 12 := by
    by_contra hnot
    have hstep := roundResidual_step stages T E 11 hc i11
    have hpaid := read_block_removed_lane .north _ _ _ _ hstep.1 hq11 hnot
    have hxguard := prefix_touches p .north _ _ hpaid
    obtain ⟨g, hgx, hgy, hg⟩ := actual_guard_marker l p q.1 hxguard
    have hg12 := guard_markers_residual l p hl hM haxes initial target hr hp hs ha hg hgy
    have hlt := round_deleted_before_retained .north _ _ hstep.1 hg12 hq11 hnot (congrArg Fin.val hgx)
    change q.2.val < g.2.val at hlt
    have hY := readDepth_le_last p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hY
    have hD := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    omega
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq13 := roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have hy := row_touches p .west _ (Or.inl rfl) ht
    apply hrows
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    exact Or.inr (Or.inr (Or.inl hy)))
  have i13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq14 := roundResidual_unread_keeps stages T E 13 hc i13 hq13 (by
    intro ht
    exact hwork (probe_rows_work l p hl hM (row_touches p .west _ (Or.inl rfl) ht)))
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq15 := (roundResidual_clear_keeps stages T E 14 hc i14 hq14).1
  have i15 : stages[15]? = some (axisReadRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, axisReadRound, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq16 := roundResidual_unread_keeps stages T E 15 hc i15 hq15 (fun ht => hcol (axis_touch_street l p hl ht))
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq17 := (roundResidual_clear_keeps stages T E 16 hc i16 hq16).1
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have h17 := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).2
  apply h17
  refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, ?_⟩
  intro hkeep
  simp only [thirdRowKeep, Finset.mem_union, Finset.mem_singleton] at hkeep
  rcases hkeep with (hy | hy) | hy
  · exact hwork hy
  · exact hcut hy
  · apply hrows
    change q.2.val = p.D + 4 at hy
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton]
    exact Or.inr (Or.inr (Or.inr hy))

end PushPuzzle.Push.AcceptanceSoundness

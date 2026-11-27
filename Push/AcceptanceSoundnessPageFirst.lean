/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportPrivate
public import Push.AcceptanceSoundnessPageCoordinatesSupport
import all Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceSoundnessSupportFirst
import all Push.AcceptanceSoundnessCentralSamples
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgram

/-! The actual early quotas and zero-loss row clears certify the first separate-page support. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

-- The sixteen early read blocks require a single exhaustive residual classification.
set_option maxHeartbeats 600000 in
/-- An off-page nonworking hole survives the actual early reads through the third row clear. -/
theorem canonical_off_page_residual_eighteen (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hqE : q ∈ PushS.holes t) (hcentral : q ∉ l.centralMarkers p)
    (hwork : q.2.val ∉ workRows l p) (hvert : q ∉ (l.twoPageStreets p hl).vertical) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 18 := by
  have hqfill : q ∉ (Blocked.fill t (l.centralMarkers p)).boxes := by
    simpa only [Blocked.fill, Finset.mem_union, not_or] using And.intro ((PushS.mem_holes _).mp hqE) hcentral
  have hmain : q.1 ∉ l.mainColumnSet p := fun hm => hvert (Or.inl hm)
  have hxStreet : q.1 ∈ l.streetColumnSet p :=
    (canonical_central_filled_supported_at l p hl hM haxes initial target hr .refl ha q hqfill).resolve_right
      (fun hy => hwork ((working_rows_iff l p q.2).mpr hy))
  have haxis : q.1.val ∉ axes l p := by
    intro hx
    obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, he.symm⟩)))
  have haux : q.1.val ∈ auxiliaries l p := by
    apply Finset.mem_sdiff.mpr
    refine ⟨List.mem_toFinset.mpr hxStreet, ?_⟩
    intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · exact haxis hx
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with hx | hx
      · exact hmain ((l.mainColumnSet_iff p q.1).mpr (Or.inl hx))
      · exact hmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inl hx)))
  have hframe : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    · exact hwork (by simp [workRows, hd])
    · exact hmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inl (by omega))))
    · apply hwork
      have he : q.2.val = p.H := by omega
      simp [workRows, he]
    · exact hmain ((l.mainColumnSet_iff p q.1).mpr (Or.inl hd))
  have hnewRows : q.2.val ∉ newMarkerRows p := by
    intro hy
    exact hcentral (newCentralMarkers_subset l p (program_new_rows_stock l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hqE hframe hy))
  have hguard := l.acceptanceAux_not_guard p haux
  have trim_no_touch (side : Side)
      (hhalf : if side = .upper then q.2.val ≤ p.D else p.D ≤ q.2.val) : ¬ReadTouches (trimRound l p side) q := by
    intro ht
    obtain ⟨request, hrequest, hx⟩ := ht
    obtain ⟨a, hac, he⟩ := List.mem_map.mp hrequest
    have hcol : q.1.val = a.column := by cases side <;> simpa only [← he, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
    have hpcol : q.1 ∈ l.pageColumnSet p side := by
      change q.1.val ∈ l.pageColumnCoordinates p side
      rw [hcol]
      exact acceptance_column_page l p side (List.mem_filter.mp hac).1
    apply hvert
    cases side
    · exact Or.inr (Or.inl ⟨hpcol, hhalf⟩)
    · exact Or.inr (Or.inr ⟨hpcol, hhalf⟩)
  have private_no_touch (hhalf : p.D ≤ q.2.val) : ¬ReadTouches (privateRound l p) q := by
    intro ht
    have hx := prefix_touches p .south (privateColumns l p) _ ht
    obtain ⟨a, hac, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    have hpcol : q.1 ∈ l.pageColumnSet p .lower := by
      change q.1.val ∈ l.pageColumnCoordinates p .lower
      change a.column = q.1.val at he
      rw [← he]
      exact acceptance_column_page l p .lower (List.mem_filter.mp hac).1
    exact hvert (Or.inr (Or.inr ⟨hpcol, hhalf⟩))
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let up : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D - 2, by omega⟩)
  let down : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D + 2, by omega⟩)
  have hup := auxiliary_flank_marker l p (q := up) haux (Or.inl rfl)
  have hdown := auxiliary_flank_marker l p (q := down) haux (Or.inr rfl)
  have hup10 := flank_markers_residual l p hl hM haxes initial target hr
    (canonical_initial_frame l p hl hM haxes initial target)
    (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hup) (Or.inl rfl)
  have hdown10 := flank_markers_residual l p hl hM haxes initial target hr
    (canonical_initial_frame l p hl hM haxes initial target)
    (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hdown) (Or.inr rfl)
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
  have hq3 : q ∈ roundResidual stages T E 3 := by
    unfold roundResidual
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr
        (canonical_initial_holes l p hl hM haxes initial target) ha]
    exact Finset.mem_sdiff.mpr ⟨hqE, hframe⟩
  have i3 : stages[3]? = some (trimRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq4 : q ∈ roundResidual stages T E 4 := by
    by_cases hh : p.D ≤ q.2.val
    · exact roundResidual_unread_keeps stages T E 3 hc i3 hq3 (trim_no_touch .lower hh)
    · exact roundResidual_marker_keeps stages T E 3 10 hc i3 hdown10 (by omega) hq3 rfl (by
        change p.H - (p.D + 2) ≤ p.H - q.2.val
        omega)
  have i4 : stages[4]? = some (trimRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq5 : q ∈ roundResidual stages T E 5 := by
    by_cases hh : q.2.val ≤ p.D
    · exact roundResidual_unread_keeps stages T E 4 hc i4 hq4 (trim_no_touch .upper hh)
    · exact roundResidual_marker_keeps stages T E 4 10 hc i4 hup10 (by omega) hq4 rfl (by
        change p.D - 2 ≤ q.2.val
        omega)
  have i5 : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq6 := (roundResidual_clear_keeps stages T E 5 hc i5 hq5).1
  have i6 : stages[6]? = some (mainRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainTop, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, ite_true]
  have hq7 := roundResidual_unread_keeps stages T E 6 hc i6 hq6 (fun ht => haxis (main_touch_axis l p hl .upper ht))
  have i7 : stages[7]? = some (mainRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainBottom, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, reduceCtorEq, ite_false]
  have hq8 := roundResidual_unread_keeps stages T E 7 hc i7 hq7 (fun ht => haxis (main_touch_axis l p hl .lower ht))
  have i8 : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq9 := (roundResidual_clear_keeps stages T E 8 hc i8 hq8).1
  have i9 : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq10 : q ∈ roundResidual stages T E 10 := by
    by_cases hh : p.D ≤ q.2.val
    · exact roundResidual_unread_keeps stages T E 9 hc i9 hq9 (private_no_touch hh)
    · exact roundResidual_marker_keeps stages T E 9 10 hc i9 hdown10 le_rfl hq9 rfl (by
        change p.H - (p.D + 2) ≤ p.H - q.2.val
        omega)
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have hh := row_touches p .east _ (Or.inr rfl) ht
    apply hnewRows
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    rcases hh with hh | hh
    · exact Or.inl hh
    · exact Or.inr (Or.inl hh))
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 := roundResidual_unread_keeps stages T E 11 hc i11 hq11 (fun ht => hguard (prefix_touches p .north _ _ ht))
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq13 := roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    exact hnewRows (by simp [newMarkerRows, hh]))
  have i13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq14 := roundResidual_unread_keeps stages T E 13 hc i13 hq13 (fun ht => hwork (probe_rows_work l p hl hM (row_touches p .west _ (Or.inl rfl) ht)))
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq15 := (roundResidual_clear_keeps stages T E 14 hc i14 hq14).1
  have i15 : stages[15]? = some (axisReadRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, axisReadRound, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq16 := roundResidual_unread_keeps stages T E 15 hc i15 hq15 (fun ht => haxis (axis_touch_axis l p hl ht))
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq17 := (roundResidual_clear_keeps stages T E 16 hc i16 hq16).1
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  exact (roundResidual_clear_keeps stages T E 17 hc i17 hq17).1

/-- Filling the permanent central markers leaves the real accepted endpoint on the first separate-page sparse support. -/
theorem canonical_terminal_page_first_supported (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (twoPageFirst l p hl).support (Blocked.fill t (l.centralMarkers p)) := by
  intro q hq
  have hqE : q ∈ PushS.holes t := (PushS.mem_holes _).mpr (fun hb => hq (Finset.mem_union_left _ hb))
  have hcentral : q ∉ l.centralMarkers p := fun hm => hq (Finset.mem_union_right _ hm)
  by_contra hout
  have hwork : q.2.val ∉ workRows l p := fun hy => hout (Or.inl (Or.inl ((working_rows_iff l p q.2).mp hy)))
  have hcut : q.2.val ∉ cutRows p := fun hy => hout (Or.inl (Or.inr hy))
  have hvert : q ∉ (l.twoPageStreets p hl).vertical := fun hv => hout (Or.inr hv)
  have hq18 := canonical_off_page_residual_eighteen l p hl hM haxes initial target hr ha hqE hcentral hwork hvert
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq17 := roundResidual_antitone stages T E hc (by omega : 17 ≤ 18) hq18
  have hkept := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).2
  apply hkept
  apply Finset.mem_sdiff.mpr
  refine ⟨Finset.mem_range.mpr q.2.isLt, ?_⟩
  simp only [thirdRowKeep, Finset.mem_union, Finset.mem_singleton]
  rintro ((hw | hc) | hs)
  · exact hwork hw
  · exact hcut hc
  · change q.2.val = p.D + 4 at hs
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 18 (by omega) hq18
    exact hcentral (newCentralMarkers_subset l p (program_new_rows_stock l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hqE hf (by simp [hs])))

end PushPuzzle.Push.AcceptanceSoundness

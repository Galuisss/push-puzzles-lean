/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCut
public import Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessSupportFirst
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all PushS.PortEndpointLocality
import all PushS.PortSegments

/-! Original central-cut holes survive the actual first twenty-five acceptance blocks. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem main_touch_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (mainRound l p side) q) : q.1.val ∈ axes l p := by
  obtain ⟨request, hr, hx⟩ := ht
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hr
  have hcol : q.1.val = p.x e.port := by cases side <;> simpa only [← heq, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl (List.mem_filter.mp he).1), hcol.symm⟩)

private theorem axis_touch_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (axisReadRound l p) q) : q.1.val ∈ axes l p := by
  obtain ⟨a, ha, hx⟩ := ht
  change q.1.val = a.1 at hx
  rcases List.mem_append.mp ha with ha | ha
  · exact hx.symm ▸ (Finset.mem_sdiff.mp ((mem_prefixRequests _ _ _ _).mp ha).1).1
  · exact hx.symm ▸ l.acceptanceCore_subset_axes p hl ((mem_prefixRequests _ _ _ _).mp ha).1

set_option maxHeartbeats 600000 in
/-- Every genuine old central marker remains unpaid through the actual non-street column clear. -/
theorem canonical_cut_residual_twentyfive (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 25 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hp0 := canonical_initial_frame l p hl hM haxes initial target
  have hs0 := canonical_initial_holes l p hl hM haxes initial target
  have hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E :=
    (program_clean_execution l p hl hM haxes initial target hr hs0 ha).2
  have hqE := canonical_central_cut_empty_at l p hl hM haxes initial target hr .refl ha hq hy
  have hframe := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hq).1).2
  have haux := l.acceptanceOriginalAux_mem p hl hM haxes
    (l.acceptanceCutAux p (l.canonical initial) (l.centralMarkers_subset_encoded p _ hq) hframe hy)
  have haxis : q.1.val ∉ axes l p := fun hx => (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ hx)
  have hguard : q.1.val ∉ guards l p := by
    intro hx
    exact guard_not_street l p (l.fixedSegments p) (List.mem_toFinset.mp (Finset.mem_sdiff.mp haux).1) (List.mem_toFinset.mp hx)
  have hwork : q.2.val ∉ workRows l p := by
    intro hw
    have hgap := work_rows_central_gap l p hw
    omega
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let up : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D - 2, by omega⟩)
  let down : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D + 2, by omega⟩)
  have hup := auxiliary_flank_marker l p (q := up) haux (Or.inl rfl)
  have hdown := auxiliary_flank_marker l p (q := down) haux (Or.inr rfl)
  have hup10 := flank_markers_residual l p hl hM haxes initial target hr hp0 hs0 ha
    (newCentralMarkers_subset l p hup) (Or.inl rfl)
  have hdown10 := flank_markers_residual l p hl hM haxes initial target hr hp0 hs0 ha
    (newCentralMarkers_subset l p hdown) (Or.inr rfl)
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
    rfl
  have hq3 : q ∈ roundResidual stages T E 3 := by
    unfold roundResidual
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr hs0 ha]
    exact Finset.mem_sdiff.mpr ⟨hqE, hframe⟩
  have i3 : stages[3]? = some (trimRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq4 := roundResidual_marker_keeps stages T E 3 10 hc i3 hdown10 (by omega) hq3 rfl (by
    change p.H - (p.D + 2) ≤ p.H - q.2.val
    omega)
  have i4 : stages[4]? = some (trimRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq5 := roundResidual_marker_keeps stages T E 4 10 hc i4 hup10 (by omega) hq4 rfl (by
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
  have hq10 := roundResidual_marker_keeps stages T E 9 10 hc i9 hdown10 le_rfl hq9 rfl (by
    change p.H - (p.D + 2) ≤ p.H - q.2.val
    omega)
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have hh := row_touches p .east _ (Or.inr rfl) ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega)
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 := roundResidual_unread_keeps stages T E 11 hc i11 hq11 (fun ht => hguard (prefix_touches p .north _ _ ht))
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq13 := roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    omega)
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
  have hq18 := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).1
  have i18 : stages[18]? = some (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq19 := roundResidual_unread_keeps stages T E 18 hc i18 hq18 (fun ht => haxis (l.acceptanceCore_subset_axes p hl (prefix_touches p .north _ _ ht)))
  have i19 : stages[19]? = some (readColumns p .south (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq20 := roundResidual_unread_keeps stages T E 19 hc i19 hq19 (fun ht => hguard (prefix_touches p .south _ _ ht))
  have i20 : stages[20]? = some (.clear .north (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq21 := (roundResidual_clear_keeps stages T E 20 hc i20 hq20).1
  have i21 : stages[21]? = some (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq22 : q ∈ roundResidual stages T E 22 := by
    by_cases hx : q.1.val ∈ samples l p
    · obtain ⟨g, hgx, hgy, hg⟩ := actual_sample_marker l p q.1 hx
      have hg22 := sample_markers_residual l p hl hM haxes initial target hr hp0 hs0 ha
        (newCentralMarkers_subset l p hg) hgy
      exact roundResidual_marker_keeps stages T E 21 22 hc i21 hg22 le_rfl hq21 (congrArg Fin.val hgx) (by
        change p.H - g.2.val ≤ p.H - q.2.val
        omega)
    · exact roundResidual_unread_keeps stages T E 21 hc i21 hq21 (fun ht => hx (prefix_touches p .south _ _ ht))
  have i22 : stages[22]? = some (readRows p .east {p.D + 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq23 := roundResidual_unread_keeps stages T E 22 hc i22 hq22 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .east _ (Or.inr rfl) ht)
    omega)
  have i23 : stages[23]? = some (readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq24 := roundResidual_unread_keeps stages T E 23 hc i23 hq23 (fun ht => hwork (Finset.mem_sdiff.mp (row_touches p .west _ (Or.inl rfl) ht)).1)
  have i24 : stages[24]? = some (.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  exact (roundResidual_clear_keeps stages T E 24 hc i24 hq24).1

end PushPuzzle.Push.AcceptanceSoundness

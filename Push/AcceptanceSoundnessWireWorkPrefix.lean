/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireGuard
import all Push.AcceptanceProgramWireRowStockSlots
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceSoundnessSupportFirst
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushFS.Grid

/-! After both public trims, actual ordinary-rail holes survive every read up to the working-row block. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- No read between R5 and R23 consumes an actual accepted ordinary-rail hole. -/
theorem canonical_wire_five_to_work {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrail : q ∈ wireOpenRail p g)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 5) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 23 := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let E := PushS.holes t
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hqE := scan_subset (roundResidual_eval stages T E 5 hc) hq
  have haxis := canonical_wire_hole_not_axis l p hl hM haxes initial target hgate hg hw hr ha hqE hrail
  have hguards := canonical_wire_hole_not_guard l p hl hM haxes initial target hgate hg hw hr ha hqE hrail
  have hcore : q.1.val ∉ cores l p := fun h => haxis (cores_subset_axes l p hl h)
  obtain ⟨hj, hjM⟩ := placement_level_bounds l hl hg
  have hjm := hjM.trans hM
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p g.level
  have hH : p.H = 2 * p.D := rfl
  have hrow := (Finset.mem_filter.mp hrail).2.1
  have hy : q.2.val = wireWorkRow p g.side g.level := by
    simpa only [wireWorkRow, readDepth_eq p hj hjm] using hrow
  have hprobe : q.2.val ∉ probeRows l p := hy ▸ wireWorkRow_not_probe l p hl hM g.side hj hjm
  have hcentral : q.2.val ∉ newMarkerRows p := by
    cases hs : g.side <;> simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton,
      hs, ite_true, reduceCtorEq, ite_false] at hrow ⊢ <;> omega
  have i5 : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq6 := (roundResidual_clear_keeps stages T E 5 hc i5 hq).1
  have i6 : stages[6]? = some (mainRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainTop, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, ite_true]
  have hq7 := roundResidual_unread_keeps stages T E 6 hc i6 hq6
    (fun ht => haxis (main_touch_axis l p hl .upper ht))
  have i7 : stages[7]? = some (mainRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainBottom, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero, reduceCtorEq, ite_false]
  have hq8 := roundResidual_unread_keeps stages T E 7 hc i7 hq7
    (fun ht => haxis (main_touch_axis l p hl .lower ht))
  have i8 : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq9 := (roundResidual_clear_keeps stages T E 8 hc i8 hq8).1
  have i9 : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq10 : q ∈ roundResidual stages T E 10 := by
    by_cases hx : q.1.val ∈ privateColumns l p
    · have hs : g.side = .upper := by
        cases hs : g.side
        · rfl
        · exact False.elim (canonical_wire_lower_hole_not_private l p hl hM haxes initial target hgate
            hg hw hs hr ha hqE hrail hx)
      have haux := private_column_aux l p hl hM haxes hx
      let down : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D + 2, by omega⟩)
      have hd := auxiliary_flank_marker l p (q := down) haux (Or.inr rfl)
      have hd10 := flank_markers_residual l p hl hM haxes initial target hr
        (canonical_initial_frame l p hl hM haxes initial target)
        (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hd) (Or.inr rfl)
      apply roundResidual_marker_keeps stages T E 9 10 hc i9 hd10 le_rfl hq9 rfl
      change p.H - (p.D + 2) ≤ p.H - q.2.val
      simp only [hs, ite_true] at hrow
      omega
    · exact roundResidual_unread_keeps stages T E 9 hc i9 hq9
        (fun ht => hx (prefix_touches p .south _ _ ht))
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have hh := row_touches p .east _ (Or.inr rfl) ht
    apply hcentral
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hh ⊢
    exact hh.elim (fun h => Or.inl h) (fun h => Or.inr (Or.inl h)))
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 := roundResidual_unread_keeps stages T E 11 hc i11 hq11
    (fun ht => hguards (prefix_touches p .north _ _ ht))
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq13 := roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    exact hcentral (by simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inl hh))))
  have i13 : stages[13]? = some (readRows p .west (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq14 := roundResidual_unread_keeps stages T E 13 hc i13 hq13
    (fun ht => hprobe (row_touches p .west _ (Or.inl rfl) ht))
  have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq15 := (roundResidual_clear_keeps stages T E 14 hc i14 hq14).1
  have i15 : stages[15]? = some (axisReadRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, axisReadRound, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq16 := roundResidual_unread_keeps stages T E 15 hc i15 hq15 (by
    intro ht
    obtain ⟨request, hrequest, hx⟩ := ht
    rcases List.mem_append.mp hrequest with hrequest | hrequest
    · exact haxis (Finset.mem_sdiff.mp (hx.symm ▸ (mem_prefixRequests _ _ _ _).mp hrequest |>.1)).1
    · exact hcore (hx.symm ▸ (mem_prefixRequests _ _ _ _).mp hrequest |>.1))
  have i16 : stages[16]? = some (.clear .north (axes l p \ cores l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq17 := (roundResidual_clear_keeps stages T E 16 hc i16 hq16).1
  have i17 : stages[17]? = some (.clear .west (Finset.range (p.H + 1) \ thirdRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, thirdRowKeep, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq18 := (roundResidual_clear_keeps stages T E 17 hc i17 hq17).1
  have i18 : stages[18]? = some (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq19 := roundResidual_unread_keeps stages T E 18 hc i18 hq18
    (fun ht => hcore (prefix_touches p .north _ _ ht))
  have i19 : stages[19]? = some (readColumns p .south (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq20 := roundResidual_unread_keeps stages T E 19 hc i19 hq19
    (fun ht => hguards (prefix_touches p .south _ _ ht))
  have i20 : stages[20]? = some (.clear .north (guards l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq21 := (roundResidual_clear_keeps stages T E 20 hc i20 hq20).1
  have i21 : stages[21]? = some (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq22 : q ∈ roundResidual stages T E 22 := by
    by_cases hx : q.1.val ∈ samples l p
    · have hs : g.side = .upper := by
        cases hs : g.side
        · rfl
        · exact False.elim (canonical_wire_lower_hole_not_sample l p hl hM haxes initial target hgate
            hg hw hs hr ha hqE hrail hx)
      obtain ⟨down, hdx, hdy, hd⟩ := actual_sample_marker l p q.1 hx
      have hd22 := sample_markers_residual l p hl hM haxes initial target hr
        (canonical_initial_frame l p hl hM haxes initial target)
        (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hd) hdy
      apply roundResidual_marker_keeps stages T E 21 22 hc i21 hd22 le_rfl hq21 (congrArg Fin.val hdx)
      change p.H - down.2.val ≤ p.H - q.2.val
      simp only [hs, ite_true] at hrow
      omega
    · exact roundResidual_unread_keeps stages T E 21 hc i21 hq21
        (fun ht => hx (prefix_touches p .south _ _ ht))
  have i22 : stages[22]? = some (readRows p .east {p.D + 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  exact roundResidual_unread_keeps stages T E 22 hc i22 hq22 (by
    intro ht
    have hh := Finset.mem_singleton.mp (row_touches p .east _ (Or.inr rfl) ht)
    exact hcentral (by simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton]; exact Or.inr (Or.inr (Or.inr hh))))

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

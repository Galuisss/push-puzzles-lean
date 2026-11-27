/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramColumns
public import PushS.PortCentralStrip
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramColumns
import all PushS.PortTwoPageStreets
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortWideGeometry
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! At the central cut the real marked target contains only original auxiliary-column markers. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Actual working rows lie strictly outside the full central acceptance band. -/
theorem work_rows_central_gap (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q.2.val ∈ workRows l p) :
    q.2.val + 4 < p.D ∨ p.D + 4 < q.2.val := by
  have hr : q.2 ∈ l.workingRowSet p := List.mem_toFinset.mp hq
  have hh := l.workingRowSet_central_gap p hr
  have hD := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at hD
  have hH : p.H = 2 * p.D := rfl
  omega

/-- Of the actual acceptance-cut rows, only the central cut meets the central acceptance band. -/
theorem cut_rows_central (p : Scales.Parameters) {row : ℕ} (hr : row ∈ cutRows p)
    (hb : p.D ≤ row + 4 ∧ row ≤ p.D + 4) : row = p.D := by
  have hH : p.H = 2 * p.D := rfl
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with (he | he) | hr
  · exact he
  · have hD := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hD
    omega
  · obtain ⟨j, hj, hr⟩ := List.mem_flatMap.mp hr
    have hj := List.mem_range.mp hj
    have hD0 := readDepth_add_lt_D p (j + 1)
    have hD1 := readDepth_add_lt_D p (j + 2)
    rw [readDepth_eq p (by omega) (by omega)] at hD0
    rw [readDepth_eq p (by omega) (by omega)] at hD1
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with he | he <;> omega

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem raw_cut_aux (l : PortLayout) (p : Scales.Parameters) {s : Segment}
    (hs : s ∈ interiorFixed l (coordinates p)) {q : Cell (p.W + 1) (p.H + 1)}
    (hc : s.Contains (q.1.val, q.2.val)) (hy : q.2.val = p.D) :
    q.1.val ∈ originalAuxiliary l (coordinates p) := by
  simp only [interiorFixed, List.mem_append, List.mem_flatMap, List.mem_map, or_assoc] at hs
  rcases hs with ⟨e, he, hs⟩ | ⟨i, hi, hs⟩ | hs | hs | ⟨x, hx, rfl⟩
  · have hp := fixed_endpoint_page l p e ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    cases he : e.side <;> simp only [he, ite_true, ite_false, reduceCtorEq] at hp <;> omega
  · have hp := gate_fixed_page p i ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    omega
  · have hp := wideFixed_is_point l p .upper hs
    obtain ⟨y, hv, hr⟩ := wideFixed_working_row l p .upper hs
    have hqy : q.2.val = s.start.2 := by simp only [Segment.Contains, ← hp] at hc; omega
    have hw : q.2.val ∈ workRows l p := hqy.symm ▸ hr.symm ▸ working_row_mem l p .upper hv
    have hh := work_rows_central_gap l p hw
    omega
  · have hp := wideFixed_is_point l p .lower hs
    obtain ⟨y, hv, hr⟩ := wideFixed_working_row l p .lower hs
    have hqy : q.2.val = s.start.2 := by simp only [Segment.Contains, ← hp] at hc; omega
    have hw : q.2.val ∈ workRows l p := hqy.symm ▸ hr.symm ▸ working_row_mem l p .lower hv
    have hh := work_rows_central_gap l p hw
    omega
  · have hxq := (point_coordinates hc).1
    dsimp only at hxq
    exact hxq.symm ▸ hx

/-- Every actual marked target cell on the central cut lies on an original auxiliary column. -/
theorem acceptanceCutAux (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) (hy : q.2.val = p.D) :
    q.1.val ∈ l.acceptanceAuxiliaryCoordinates p := by
  change q.1.val ∈ originalAuxiliary l (coordinates p)
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact False.elim (hf (frame_contains (coordinates p) q ⟨s, hs, hc⟩))
    unfold markedInterior at hs
    extract_lets base guards shifted aux marked at hs
    change s ∈ ((shifted ++ _) ++ _) ++ _ at hs
    simp only [List.mem_append, or_assoc] at hs
    rcases hs with hs | hs | hs | hs
    · dsimp only [shifted] at hs
      split at hs
      next hadj =>
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
        unfold shiftPoint at hc
        split at hc
        next hshift =>
          have hp := (point_coordinates hc).2
          dsimp only at hp
          have hrow := List.contains_iff_mem.mp hshift.2.2
          have hrow' : p.D ∈ streetRows (coordinates p) := (hp.symm.trans hy) ▸ hrow
          exact False.elim (cut_not_streetRow p hrow')
        next hshift => exact raw_cut_aux l p ht hc hy
      next hadj => exact raw_cut_aux l p hs hc hy
    · obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        have hp := (point_coordinates hc).2
        have hD := readDepth_add_lt_D p 0
        dsimp only [coordinates, Prod.snd] at hp
        omega
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
      have hp := (point_coordinates hc).2
      have hD := readDepth_add_lt_D p 0
      dsimp only [coordinates, Prod.snd] at hp
      omega
    · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        have hp := (point_coordinates hc).2
        dsimp only [coordinates, Prod.snd] at hp
        omega
  · have hp := l.signalSegments_central_gap p state ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    dsimp only at hp
    omega

end PushPuzzle.PushS.PortLayout

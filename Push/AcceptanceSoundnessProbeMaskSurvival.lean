/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeTrimPaid
import all Push.AcceptanceProgramProbeStockSignals
import all Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceUpperProbeColumnsGeometry
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The literal early-reader mask preserves every original probe hole outside upper auxiliary and guard columns. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

/-- On non-main probe cells every canonical bit word has exactly the same literal fixed bitmap. -/
private theorem probe_nonmain_target_iff_fixed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (bits : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    q ∈ targetHoles l p bits ↔ q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
  constructor
  · intro hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    rcases List.mem_append.mp hs with hs | hs
    · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩
    · have hm := (signal_probe_rows l p hl hM haxes bits).mp
        ⟨(mem_pointHoles _ _).mpr ⟨s, hs, hc⟩, hrow⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hm
      have hx := congrArg (fun q : Cell (p.W + 1) (p.H + 1) => q.1.val) hi
      change p.x i.val = q.1.val at hx
      exact (hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i.val, i.isLt, hx.symm⟩)))).elim
  · intro hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The accepted non-main probe bitmap agrees with the fixed target bitmap before destructive reads begin. -/
theorem canonical_probe_nonmain_target
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    q ∈ PushS.holes t ↔ q ∈ targetHoles l p target := by
  rw [canonical_upper_probe_nonmain_constant l p hl hM haxes initial target hgate hr .refl ha hrow hnmain]
  rw [canonical_initial_holes l p hl hM haxes initial target]
  exact (probe_nonmain_target_iff_fixed l p hl hM haxes initial hrow hnmain).trans
    (probe_nonmain_target_iff_fixed l p hl hM haxes target hrow hnmain).symm

omit hgate

/-- An actual non-main probe hole outside upper-page columns and guard columns reaches the probe read unchanged. -/
theorem canonical_probe_unmasked_survives
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hqE : q ∈ PushS.holes t)
    (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p)
    (hncol : q.1 ∉ l.pageColumnSet p .upper) (hnG : q.1.val ∉ guards l p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  obtain ⟨ref, href, _, hy⟩ := probe_row_data l p hrow
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p ref.level
  rw [readDepth_eq p hj hjm] at hY hD
  have hH : p.H = 2 * p.D := rfl
  have haxis : q.1.val ∉ axes l p := by
    intro hx
    obtain ⟨i, hi, hix⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
    exact hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inr ⟨i, List.mem_range.mp hi, hix.symm⟩)))
  have hf : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    · omega
    · exact hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inr (Or.inl (by omega))))
    · omega
    · exact hnmain ((l.mainColumnSet_iff p q.1).mpr (Or.inl hd))
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
  have hq3 : q ∈ roundResidual stages T E 3 := by
    unfold roundResidual
    rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
      program_sideClear_remaining l p hl hM haxes initial target hr
        (canonical_initial_holes l p hl hM haxes initial target) ha]
    exact Finset.mem_sdiff.mpr ⟨hqE, hf⟩
  have hq4 := canonical_trim_other_half_keeps l p hl hM haxes initial target hr ha .lower
    (by simp only [reduceCtorEq, ite_false]; omega) hq3
  have i4 : stages[4]? = some (trimRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq5 := roundResidual_unread_keeps stages T E 4 hc i4 hq4 (by
    intro ht
    obtain ⟨request, hrequest, hqx⟩ := ht
    obtain ⟨a, hac, heq⟩ := List.mem_map.mp hrequest
    apply hncol
    change q.1.val ∈ l.pageColumnCoordinates p .upper
    have hcol : q.1.val = a.column := by simpa only [← heq, ite_true, Direction.lane] using hqx
    exact hcol ▸ acceptance_column_page l p .upper (List.mem_filter.mp hac).1)
  have i5 : stages[5]? = some (.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, firstRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq6 := (roundResidual_clear_keeps stages T E 5 hc i5 hq5).1
  have i6 : stages[6]? = some (mainRound l p .upper) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainTop, ite_true,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq7 := roundResidual_unread_keeps stages T E 6 hc i6 hq6
    (fun ht => haxis (main_touch_axis l p hl .upper ht))
  have i7 : stages[7]? = some (mainRound l p .lower) := by
    simp only [stages, schedule, preparation, frameSchedule, mainRound, mainBottom, reduceCtorEq, ite_false,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq8 := roundResidual_unread_keeps stages T E 7 hc i7 hq7
    (fun ht => haxis (main_touch_axis l p hl .lower ht))
  have i8 : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq9 := (roundResidual_clear_keeps stages T E 8 hc i8 hq8).1
  have i9 : stages[9]? = some (privateRound l p) := by
    simp only [stages, schedule, preparation, frameSchedule, privateRound, privateColumns,
      List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq10 : q ∈ roundResidual stages T E 10 := by
    by_cases hx : q.1.val ∈ privateColumns l p
    · have haux := private_column_aux l p hl hM haxes hx
      let down : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.D + 2, by omega⟩)
      have hd := auxiliary_flank_marker l p (q := down) haux (Or.inr rfl)
      have hd10 := flank_markers_residual l p hl hM haxes initial target hr
        (canonical_initial_frame l p hl hM haxes initial target)
        (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hd) (Or.inr rfl)
      apply roundResidual_marker_keeps stages T E 9 10 hc i9 hd10 le_rfl hq9 rfl
      change p.H - (p.D + 2) ≤ p.H - q.2.val
      omega
    · exact roundResidual_unread_keeps stages T E 9 hc i9 hq9 (fun ht => hx (prefix_touches p .south _ _ ht))
  have i10 : stages[10]? = some (readRows p .east {p.D - 2, p.D + 2}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq11 := roundResidual_unread_keeps stages T E 10 hc i10 hq10 (by
    intro ht
    have h := row_touches p .east _ (Or.inr rfl) ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    omega)
  have i11 : stages[11]? = some (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq12 := roundResidual_unread_keeps stages T E 11 hc i11 hq11 (fun ht => hnG (prefix_touches p .north _ _ ht))
  have i12 : stages[12]? = some (readRows p .west {p.D - 4}) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  exact roundResidual_unread_keeps stages T E 12 hc i12 hq12 (by
    intro ht
    have h := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    omega)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

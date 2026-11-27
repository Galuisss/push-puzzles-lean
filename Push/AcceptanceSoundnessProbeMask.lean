/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeMaskSurvival
public import Push.AcceptanceUpperProbeTrimGeometry
import all Push.AcceptanceUpperProbeColumnsGeometry
import all Push.AcceptanceProgramProbeStockSignals
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all Push.AcceptanceProgramRounds

/-! The actual R13 non-main probe bitmap is exactly the literal reference fixed mask. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Actual f/r trimming and guard saturation remove exactly the original non-main probe holes on their selected columns. -/
private theorem canonical_probe_nonmain_input_mask
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13 ↔
      q ∈ PushS.holes t ∧ q.1 ∉ l.pageColumnSet p .upper ∧ q.1.val ∉ guards l p := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  constructor
  · intro hq
    have hqE := scan_subset (roundResidual_eval stages T E 13 hc) hq
    have hqT := (canonical_probe_nonmain_target l p hl hM haxes initial target hgate hr ha hrow hnmain).mp hqE
    have hf := canonical_residual_not_frame l p hl hM haxes initial target hr ha 13 (by omega) hq
    refine ⟨hqE, ?_, ?_⟩
    · intro hcol
      obtain ⟨e, he, hs, k, hx⟩ := upper_page_auxiliary l p hl hcol hnmain
      have hq5 := roundResidual_antitone stages T E hc (show 5 ≤ 13 by omega) hq
      cases k with
      | f =>
        have hw := upper_probe_f_stock l p hl hM haxes target e he hs hrow hx hqT
        have hpaid := canonical_fwalk_trim_paid l p hl hM haxes initial target hgate e he hr ha
        have hm := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hpaid).mp
          (Finset.mem_sdiff.mpr ⟨hw, hf⟩)
        simp only [hs, ite_true] at hm
        exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hm).1).2 hq5
      | r =>
        have hw := upper_probe_r_stock l p hl hM haxes target e he hs hrow hx hqT
        have hpaid := canonical_r_corridor_paid l p hl hM haxes initial target hgate e he hr ha hw
        simp only [hs, ite_true] at hpaid
        exact (Finset.mem_sdiff.mp hpaid).2 hq5
    · intro hx
      have hpaid := canonical_guard_north_paid_of_target_stock l p hl hM haxes initial target hr ha q.1 hx
        (by
          intro r hrE hrF hrx
          exact canonical_guard_column_target_stock l p hl hM haxes initial target hgate hr ha
            (by rw [hrx]; exact hx) hrE hrF)
      obtain ⟨ref, href, _, hy⟩ := probe_row_data l p hrow
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM href
      have hD := readDepth_add_lt_D p ref.level
      rw [readDepth_eq p hj hjm] at hD
      have hm : q ∈ guardNorthStock l p target q.1.val :=
        Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hqT, hf⟩, rfl, by omega⟩
      have hm' := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hpaid).mp hm
      have hn := (Finset.mem_sdiff.mp hm').2
      exact hn (Finset.mem_filter.mpr ⟨roundResidual_antitone stages T E hc (show 12 ≤ 13 by omega) hq, rfl⟩)
  · rintro ⟨hq, hcol, hG⟩
    exact canonical_probe_unmasked_survives l p hl hM haxes initial target hr ha hq hrow hnmain hcol hG

/-- An actual accepted input and the genuine canonical reference have identical R13 non-main probe stock. -/
theorem canonical_probe_nonmain_reference
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hrow : q.2.val ∈ probeRows l p) (hnmain : q.1 ∉ l.mainColumnSet p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 13 ↔
      q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 13)
        (targetHoles l p target)).remaining := by
  let J := l.canonicalInstance p hl hM haxes target target
  have hJ : PushS.holes J.initial = targetHoles l p target := canonical_initial_holes l p hl hM haxes target target
  have haJ : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes J.initial) := by
    rw [hJ]
    exact ⟨∅, program_accepts_target l p target⟩
  have hmask := canonical_probe_nonmain_input_mask l p hl hM haxes initial target hgate hr ha hrow hnmain
  rw [canonical_probe_nonmain_target l p hl hM haxes initial target hgate hr ha hrow hnmain] at hmask
  have hcanonical := canonical_probe_nonmain_input_mask l p hl hM haxes target target hgate .refl haJ hrow hnmain
  have hcanonical' : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (targetHoles l p target) 13 ↔
      q ∈ targetHoles l p target ∧ q.1 ∉ l.pageColumnSet p .upper ∧ q.1.val ∉ guards l p := by
    have he := congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) =>
      q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) E 13 ↔
        q ∈ E ∧ q.1 ∉ l.pageColumnSet p .upper ∧ q.1.val ∉ guards l p) hJ
    exact he.mp hcanonical
  have hremain : roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (targetHoles l p target) 13 =
      (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 13)
        (targetHoles l p target)).remaining := by
    simp only [roundResidual, emit_eval, Option.getD_some]
  rw [hremain] at hcanonical'
  exact hmask.trans hcanonical'.symm

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

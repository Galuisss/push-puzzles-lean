/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGatePublicSamplesGeometry
public import Push.AcceptanceSoundnessWireTrimStock
import all Push.AcceptanceProgramTrimStock
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! Actual lower public trims certify their gate's target work-row samples. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hi

/-- Every canonical target work-row sample on a genuine public gate column is present at the accepted endpoint. -/
theorem canonical_gate_public_sample_terminal {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {sample : Cell (p.W + 1) (p.H + 1)} (hx : sample.1.val ∈ gatePublicColumns p middle)
    (hy : sample.2.val = p.H - readDepth p 1) (htarget : sample ∈ targetHoles l p target) : sample ∈ holes t := by
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let R := (emit (stages.take 3) T).remaining
  let A := roundResidual stages T (holes t) 3
  let F := roundResidual stages T (holes t) 4
  let requests := ((AcceptanceProgram.pageColumns l p .lower).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  let B : Finset (Cell (p.W + 1) (p.H + 1)) := Finset.univ.filter fun q =>
    q.1.val = sample.1.val ∧ 1 ≤ p.H - q.2.val ∧ p.H - q.2.val ≤ p.Y 1
  let a : PageColumn := ⟨sample.1.val, 1, false⟩
  have hac : a ∈ AcceptanceProgram.pageColumns l p .lower := gate_public_column_mem l p hi hx
  have bounds := pageColumn_bounds l p hl hM haxes .lower hac
  have depth := readDepth_eq p (show 1 ≤ 1 by omega) p.levels_pos
  have Y := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have margin := readDepth_add_lt_H p 1
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) accepted).2
  have i3 : stages[3]? = some (.read .south requests) := by
    simp only [stages, schedule, preparation, frameSchedule, requests, trimRound,
      reduceCtorEq, ite_false, List.cons_append, List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have htake : stages.take 3 = trimBeforeSchedule l p target .lower := by
    simp only [stages, schedule, preparation, frameSchedule, trimBeforeSchedule, sideClearSchedule,
      reduceCtorEq, ite_false, List.append_nil, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero, T]
  have hread := (roundResidual_step stages T (holes t) 3 hc i3).1
  have source : B ⊆ R.filter fun q => q.1.val = sample.1.val := by
    intro q hq
    obtain ⟨_, col, positive, upper⟩ := Finset.mem_filter.mp hq
    refine Finset.mem_filter.mpr ⟨?_, col⟩
    dsimp only [R]
    rw [htake]
    by_cases before : p.H - q.2.val < p.Y 1
    · exact corridor_before_trim l p hl hM haxes target .lower hac rfl col positive before
    · have same : q = sample := by
        have qb := q.2.isLt
        apply Prod.ext (Fin.ext col) (Fin.ext ?_)
        omega
      subst q
      rw [trimBeforeSchedule, ite_eq_right (by decide), List.append_nil,
        sideClear_target_remaining l p hl haxes target]
      refine Finset.mem_sdiff.mpr ⟨htarget, ?_⟩
      intro hf
      obtain ⟨d, hd⟩ := (Boundary.mem_frame sample).mp hf
      have port0 : 0 < sample.1.val := bounds.2.2.1
      have portW : sample.1.val < p.W := bounds.2.2.2
      cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega
  have region : B ⊆ (trimRound l p .lower).region := by
    intro q hq
    obtain ⟨_, col, positive, upper⟩ := Finset.mem_filter.mp hq
    have next := trimDepth_gt_work p (show 1 ≤ 1 by omega) p.levels_pos
    exact (mem_trim_region l p .lower q).mpr ⟨a, hac, rfl, col, by change p.H - q.2.val < trimDepth p 1; omega⟩
  have paid : A.filter (fun q => Direction.south.lane q = sample.1.val) \
      F.filter (fun q => Direction.south.lane q = sample.1.val) ⊆ B := by
    intro q hq
    obtain ⟨hqA, hqF⟩ := Finset.mem_sdiff.mp hq
    obtain ⟨hqA, col⟩ := Finset.mem_filter.mp hqA
    change q.1.val = sample.1.val at col
    have notF : q ∉ F := fun h => hqF (Finset.mem_filter.mpr ⟨h, col⟩)
    have far := canonical_trim_payment_depth l p hl hM haxes initial target hr accepted .lower hac col hqA notF
    have central := canonical_trim_payment_not_central l p hl hM haxes initial target hr accepted .lower notF
    have hole := scan_subset (roundResidual_eval stages T (holes t) 3 hc) hqA
    have near : p.H - q.2.val ≤ readDepth p 1 := by
      by_contra hn
      exact (mem_holes q).mp hole (canonical_gate_public_trim_deep_occupied l p hl hM haxes initial target hi hgate
        (col.symm ▸ hx) (by omega) far central hr .refl accepted)
    have notFrame := canonical_residual_not_frame l p hl hM haxes initial target hr accepted 3 (by omega) hqA
    have positive : 1 ≤ p.H - q.2.val := by
      by_contra hn
      apply notFrame
      have qb := q.2.isLt
      exact (Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, col, positive, by omega⟩
  have href : ((emit [.read .south requests] R).remaining.filter fun q => Direction.south.lane q = sample.1.val).card +
      B.card ≤ (R.filter fun q => Direction.south.lane q = sample.1.val).card := by
    let U := (emit [.read .south requests] R).remaining.filter fun q => q.1.val = sample.1.val
    have out : U ⊆ R.filter fun q => q.1.val = sample.1.val :=
      Finset.filter_subset_filter _ (emit_remaining_subset _ _)
    have disjoint : Disjoint U B := by
      apply Finset.disjoint_left.mpr
      intro q hq hb
      have absent := (Finset.mem_filter.mp hq).1
      have same : (.read .south requests : Template) = trimRound l p .lower := rfl
      rw [same] at absent
      simp only [emit_remaining, allRegions, Finset.union_empty] at absent
      exact (Finset.mem_sdiff.mp absent).2 (region hb)
    have cardinal := Finset.card_le_card (Finset.union_subset out source)
    rw [Finset.card_union_of_disjoint disjoint] at cardinal
    exact cardinal
  have saturated := round_lane_saturation .south requests R A F B sample.1.val hread paid href
  have sampleMem : sample ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by omega, by omega⟩
  have consumed := (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => sample ∈ S) saturated).mp sampleMem
  exact scan_subset (roundResidual_eval stages T (holes t) 3 hc)
    (Finset.mem_filter.mp (Finset.mem_sdiff.mp consumed).1).1

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

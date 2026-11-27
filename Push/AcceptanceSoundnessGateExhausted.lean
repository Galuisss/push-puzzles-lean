/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessGateUpperWindow
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! The actual gate-axis main and probe quotas exhaust its complete open-axis inventory at R16. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hupper : upper.side = .upper) (hport : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hg hk hu hupper hport

/-- The genuine two-hole upper main read leaves no own work-row hole on a gate middle axis. -/
private theorem canonical_gate_work_not_residual_sixteen
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = p.Y upper.level) :
    q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let A := (roundResidual stages T E 6).filter fun r => r.1.val = p.x (g.left + 1)
  let F := (roundResidual stages T E 7).filter fun r => r.1.val = p.x (g.left + 1)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i6 : stages[6]? = some (mainTop l p) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  intro hq16
  have hq7 := roundResidual_antitone stages T E hc (show 7 ≤ 16 by omega) hq16
  have hsub : F ⊆ A := Finset.filter_subset_filter _ (roundResidual_succ_subset stages T E 6 hc)
  have hempty : A \ F = ∅ := by
    apply Finset.eq_empty_of_forall_notMem
    intro r hrPaid
    obtain ⟨hrA, hrF⟩ := Finset.mem_sdiff.mp hrPaid
    obtain ⟨hr6, hrx⟩ := Finset.mem_filter.mp hrA
    have hrnot : r ∉ roundResidual stages T E 7 := fun h => hrF (Finset.mem_filter.mpr ⟨h, hrx⟩)
    have hlt := round_deleted_before_retained .north _ _ (roundResidual_step stages T E 6 hc i6).1
      hq7 hr6 hrnot (hx.trans hrx.symm)
    change r.2.val < q.2.val at hlt
    have hrE := scan_subset (roundResidual_eval stages T E 6 hc) hr6
    have hframe := canonical_residual_not_frame l p hl hM haxes initial target hr ha 6 (by omega) hr6
    have hr0 : 1 ≤ r.2.val := by
      by_contra hn
      exact hframe ((Boundary.mem_frame r).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
    exact (PushS.mem_holes _).mp hrE
      (canonical_gate_upper_first_rod_full l p hl hM haxes initial target hgate hg hk hu hupper hport hr ha
        hrx hr0 (by rw [readDepth_eq p hj hjm]; omega))
  have hcard := Finset.card_sdiff_add_card_eq_card hsub
  rw [hempty, Finset.card_empty, Nat.zero_add] at hcard
  have hmain := canonical_main_column_loss l p hl hM haxes initial target upper hu hr ha
  simp only [hupper, hport, ite_true, Nat.reduceAdd] at hmain
  change F.card + 2 = A.card at hmain
  omega

/-- Every actual accepted gate middle axis is exhausted by the combined main/probe/core reads, before any deficit certificate. -/
theorem canonical_gate_axis_residual_sixteen_empty
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 ∩ gateAxis p (g.left + 1) = ∅ := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  have hx := (Finset.mem_filter.mp (Finset.mem_inter.mp hq).2).2.1
  rcases canonical_gate_residual_sixteen_own_rows l p hl hM haxes initial target hgate hg hk hu hupper hport hr ha hq with hy | hy
  · exact canonical_gate_work_not_residual_sixteen l p hl hM haxes initial target hgate hg hk hu hupper hport hr ha hx hy
      (Finset.mem_inter.mp hq).1
  · have hq14 := roundResidual_antitone stages T E hc (show 14 ≤ 16 by omega) (Finset.mem_inter.mp hq).1
    have i14 : stages[14]? = some (.clear .east (probeRows l p)) := by
      simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.getElem?_cons_succ, List.getElem?_cons_zero]
    have hn := (roundResidual_clear_keeps stages T E 14 hc i14 hq14).2
    have hrow : p.Y upper.level + 2 ∈ probeRows l p := by
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨upper, List.mem_filter.mpr ⟨hu, by simp only [hupper, beq_self_eq_true]⟩, rfl⟩
    change q.2.val ∉ probeRows l p at hn
    exact hn (hy ▸ hrow)

/-- Actual gate deficit is bounded by its genuinely paid probe-column observation above the target bit. -/
theorem canonical_gate_probe_deficit
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (target.getD (g.left + 1) false).toNat +
      (Inventory.count (gateAxis p (g.left + 1)) (I).initial - Inventory.count (gateAxis p (g.left + 1)) t) ≤
      (probeColumnStock l p target (PushS.holes t) (g.left + 1)).card :=
  canonical_gate_probe_deficit_of_exhausted l p hl hM haxes initial target hg hk hu hupper hport hgate hr ha
    (canonical_gate_axis_residual_sixteen_empty l p hl hM haxes initial target hgate hg hk hu hupper hport hr ha)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

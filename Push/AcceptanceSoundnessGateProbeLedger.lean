/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessGateLastPayment
public import Push.AcceptanceProgramGateAxisReadStock
import all Push.AcceptanceProgramGateAxisReadStock
import all Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortCoreCrossing

/-! Genuine core-column payments give the gate deficit inequality once R16 is exhausted. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
  {upper : Endpoint} (hu : upper ∈ l.endpoints) (hupper : upper.side = .upper) (hport : upper.port = g.left + 1)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hg hk

/-- The actual lower ordinary main read leaves every gate-middle column unchanged. -/
theorem canonical_gate_main_lower_stock {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 8).filter (fun q => q.1.val = p.x (g.left + 1)) =
      (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 7).filter (fun q => q.1.val = p.x (g.left + 1)) := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have i7 : stages[7]? = some (mainBottom l p) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  apply Finset.Subset.antisymm (Finset.filter_subset_filter _ (roundResidual_succ_subset stages T E 7 hc))
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  refine Finset.mem_filter.mpr ⟨roundResidual_unread_keeps stages T E 7 hc i7 hq ?_, hx⟩
  intro ht
  obtain ⟨request, hrequest, hcol⟩ := ht
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hrequest
  obtain ⟨he, hs⟩ := List.mem_filter.mp he
  have hs : e.side = .lower := of_decide_eq_true hs
  have hx' : p.x e.port = p.x (g.left + 1) := by
    change q.1.val = request.1 at hcol
    have hm := congrArg Prod.fst heq
    omega
  exact l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he hs (axis_injective p hx')

include hu hupper hport

/-- The actual combined read pays precisely its canonical core quota on the genuine middle column. -/
private theorem canonical_gate_axis_read_column_loss {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    let stages := schedule l p (targetHoles l p target \ Boundary.frame).card
    let T := targetHoles l p target
    ((roundResidual stages T (PushS.holes t) 16).filter fun q => q.1.val = p.x (g.left + 1)).card +
      (2 - (target.getD (g.left + 1) false).toNat) =
      ((roundResidual stages T (PushS.holes t) 15).filter fun q => q.1.val = p.x (g.left + 1)).card := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let requests := prefixRequests (axes l p \ cores l p) (fun _ => p.H + 1) ++
    prefixRequests (cores l p) (fun _ => p.H - p.Y 1)
  let R := (emit (stages.take 15) T).remaining
  let A := roundResidual stages T E 15
  let F := roundResidual stages T E 16
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[15]? = some (.read .north requests) := by
    simp only [stages, schedule, preparation, frameSchedule, requests, List.cons_append,
      List.nil_append, List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hread := (roundResidual_step stages T E 15 hc hi).1
  have hloss := round_reference_lane_loss .north requests R A F (p.x (g.left + 1)) hread
  change (A.filter fun q => q.1.val = p.x (g.left + 1)).card +
    ((emit [.read .north requests] R).remaining.filter fun q => q.1.val = p.x (g.left + 1)).card =
    (F.filter fun q => q.1.val = p.x (g.left + 1)).card + (R.filter fun q => q.1.val = p.x (g.left + 1)).card at hloss
  have href := gate_axisRead_target_column_loss l p hl hM haxes target hg hk hu hupper hport
  change ((emit [.read .north requests] R).remaining.filter fun q => q.1.val = p.x (g.left + 1)).card +
    (2 - (target.getD (g.left + 1) false).toNat) = (R.filter fun q => q.1.val = p.x (g.left + 1)).card at href
  change (F.filter fun q => q.1.val = p.x (g.left + 1)).card + _ = (A.filter fun q => q.1.val = p.x (g.left + 1)).card
  omega

/-- The true total middle-column loss through R16 is its two main holes, paid probes and canonical core quota. -/
private theorem canonical_gate_column_payment_balance {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    let stages := schedule l p (targetHoles l p target \ Boundary.frame).card
    let T := targetHoles l p target
    ((roundResidual stages T (PushS.holes t) 16).filter fun q => q.1.val = p.x (g.left + 1)).card +
      (probeColumnStock l p target (PushS.holes t) (g.left + 1)).card + 2 +
        (2 - (target.getD (g.left + 1) false).toNat) =
      (PushS.holes t ∩ ordinaryAxis p (g.left + 1)).card := by
  have hm := canonical_main_column_loss l p hl hM haxes initial target upper hu hr ha
  simp only [hupper, hport, ite_true, Nat.reduceAdd] at hm
  have hlo := congrArg Finset.card (canonical_gate_main_lower_stock l p hl hM haxes initial target hg hk hr ha)
  have hp := gate_middle_lt l hl (placement_gate_mem l hg hk)
  have hinput := congrArg Finset.card (canonical_main_input_axis l p hl hM haxes initial target hp hr ha)
  have hkeep := congrArg Finset.card (canonical_main_to_probe_stock l p hl hM haxes initial target hp hr ha)
  have hprobe := canonical_probe_column_card l p hl hM haxes initial target (g.left + 1) hr ha
  have hread := canonical_gate_axis_read_column_loss l p hl hM haxes initial target hg hk hu hupper hport hr ha
  dsimp only at hread ⊢
  omega

/-- Exhaustion of the actual open middle axis gives the signed gate probe inequality. -/
theorem canonical_gate_probe_deficit_of_exhausted (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hexhaust : roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 16 ∩ gateAxis p (g.left + 1) = ∅) :
    (target.getD (g.left + 1) false).toNat +
      (Inventory.count (gateAxis p (g.left + 1)) (I).initial - Inventory.count (gateAxis p (g.left + 1)) t) ≤
      (probeColumnStock l p target (PushS.holes t) (g.left + 1)).card := by
  let A := (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) (PushS.holes t) 16).filter fun q => q.1.val = p.x (g.left + 1)
  let G := PushS.holes t ∩ gateAxis p (g.left + 1)
  let R := PushS.holes t ∩ ordinaryAxis p (g.left + 1)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hA : A ⊆ R := by
    intro q hq
    obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
    have hin6 := roundResidual_antitone _ _ _ hc (show 6 ≤ 16 by omega) hq
    have hsix := canonical_main_input_axis l p hl hM haxes initial target (gate_middle_lt l hl (placement_gate_mem l hg hk)) hr ha
    exact (congrArg (fun S : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ S) hsix).mp (Finset.mem_filter.mpr ⟨hin6, hx⟩)
  have hG : G ⊆ R := by
    intro q hq
    obtain ⟨hq, hgate⟩ := Finset.mem_inter.mp hq
    obtain ⟨_, hx, hy0, hy⟩ := Finset.mem_filter.mp hgate
    exact Finset.mem_inter.mpr ⟨hq, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy0, by omega⟩⟩
  have hd : Disjoint G A := by
    apply Finset.disjoint_left.mpr
    intro q hq hqa
    apply Finset.notMem_empty q
    rw [← hexhaust]
    exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hqa).1, (Finset.mem_inter.mp hq).2⟩
  have hcard := Finset.card_le_card (Finset.union_subset hG hA)
  rw [Finset.card_union_of_disjoint hd] at hcard
  have hpay := canonical_gate_column_payment_balance l p hl hM haxes initial target hg hk hu hupper hport hr ha
  have hdef := canonical_gateAxis_deficit_balance l p hl hM haxes initial target hgate hg hk hr .refl ha
  have hbit := Bool.toNat_le (target.getD (g.left + 1) false)
  change G.card = 4 + _ at hdef
  change A.card + _ + 2 + _ = R.card at hpay
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

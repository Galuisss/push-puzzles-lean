/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeColumns
public import Push.AcceptanceProgramAxisReadStock
import all Push.AcceptanceProgramAxisReadStock
import all Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! Actual main, probe and final-axis payments certify the ordinary signed probe inventory. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

/-- The actual ordinary column entering R15 pays exactly its emitted complementary target bit. -/
private theorem canonical_ordinary_axis_read_input_card {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hupper : upper.side = .upper) (hlower : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    ((roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 15).filter fun q => q.1.val = p.x upper.port).card =
      1 - (target.getD upper.port false).toNat := by
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
  have hselected : p.x upper.port ∈ axes l p \ cores l p := by
    apply Finset.mem_sdiff.mpr
    refine ⟨List.mem_toFinset.mpr (List.mem_map.mpr
      ⟨upper.port, List.mem_range.mpr (l.endpoints_port_lt hl hu), rfl⟩), ?_⟩
    simpa only [hport] using ordinary_axis_not_core l p hl lower hlow hlower
  have hzero := canonical_ordinary_axis_read_output_empty l p hl hM haxes initial target hselected hr ha
  have hloss := round_reference_lane_loss .north requests R A F (p.x upper.port) hread
  change (A.filter fun q => q.1.val = p.x upper.port).card +
    ((emit [.read .north requests] R).remaining.filter fun q => q.1.val = p.x upper.port).card =
    (F.filter fun q => q.1.val = p.x upper.port).card + (R.filter fun q => q.1.val = p.x upper.port).card at hloss
  have href := axisRead_target_column_loss l p hl hM haxes target hu hlow hupper hlower hport
  change ((emit [.read .north requests] R).remaining.filter fun q => q.1.val = p.x upper.port).card +
    (1 - (target.getD upper.port false).toNat) = (R.filter fun q => q.1.val = p.x upper.port).card at href
  change (F.filter fun q => q.1.val = p.x upper.port) = ∅ at hzero
  rw [hzero, Finset.card_empty, Nat.zero_add] at hloss
  change (A.filter fun q => q.1.val = p.x upper.port).card = _
  omega

/-- The ordinary box surplus plus its genuinely paid probe-column inventory equals the target bit. -/
theorem canonical_ordinary_probe_balance (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hupper : upper.side = .upper) (hlower : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    (Inventory.count (ordinaryAxis p upper.port) t - Inventory.count (ordinaryAxis p upper.port) (I).initial) +
      (probeColumnStock l p target (PushS.holes t) upper.port).card = (target.getD upper.port false).toNat := by
  have hb := canonical_ordinaryAxis_surplus_balance l p hl hM haxes initial target hgate
    hu hlow hupper hlower hport hr .refl ha
  have hm := canonical_ordinaryAxis_probe_input_card l p hl hM haxes initial target hu hlow hupper hlower hport hr ha
  have hc := canonical_probe_column_card l p hl hM haxes initial target upper.port hr ha
  have ht := canonical_ordinary_axis_read_input_card l p hl hM haxes initial target hu hlow hupper hlower hport hr ha
  have hbit := Bool.toNat_le (target.getD upper.port false)
  omega

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

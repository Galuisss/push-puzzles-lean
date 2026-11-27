/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessProbeRowBalance
public import Push.AcceptanceAxisClosure
import all Push.AcceptanceProbeNumerics
import all PushS.PortSignalLocality
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing

/-! The actual accepted scan cancels every signed axis error and supplies the full numerical axis certificate. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hpartners : Partner.ReaderPartners l)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hpartners

/-- The actual programme and repaired partners force exact observations and zero ordinary/gate signed errors. -/
theorem canonical_probe_inventory_errors_cancel
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) (i : Fin l.portCount) :
    AcceptanceProbeNumerics.observed l p hl target t i = (target.getD i.val false).toNat ∧
      (¬Partner.Middle l i.val → AcceptanceProbeNumerics.J p (I).initial t i = 0) ∧
      (Partner.Middle l i.val → AcceptanceProbeNumerics.D p (I).initial t i = 0) :=
  AcceptanceProbe.cancel l hl hpartners (fun i => (target.getD i.val false).toNat)
    (AcceptanceProbeNumerics.observed l p hl target t)
    (AcceptanceProbeNumerics.J p (I).initial t) (AcceptanceProbeNumerics.D p (I).initial t)
    (fun i hw => AcceptanceProbeNumerics.canonical_wire l p hl hM haxes initial target hgate hr ha i hw)
    (fun i hn => AcceptanceProbeNumerics.canonical_ordinary l p hl hM haxes initial target hgate hr ha i hn)
    (fun i hm => AcceptanceProbeNumerics.canonical_middle l p hl hM haxes initial target hgate hr ha i hm)
    (canonical_probe_row_balance l p hl hM haxes initial target hgate hr ha) i

/-- Every actual port observation equals its emitted target bit. -/
theorem canonical_probe_observed_eq_target
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) (i : Fin l.portCount) :
    AcceptanceProbeNumerics.observed l p hl target t i = (target.getD i.val false).toNat :=
  (canonical_probe_inventory_errors_cancel l p hl hM haxes initial target hgate hpartners hr ha i).1

/-- An actual accepted endpoint has all five-hole ordinary axes and four-hole gate axes, certified by the real reader. -/
theorem canonical_axis_inventories
    {t : State (p.W + 1) (p.H + 1)} (hr : Reachable (I).board none (I).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) : AxisInventories l p t := by
  constructor
  · intro upper lower hu hlow hsuSide hslSide hport
    let i : Fin l.portCount := ⟨upper.port, l.endpoints_port_lt hl hu⟩
    have hn : ¬Partner.Middle l i.val := by
      rintro ⟨kind, first, hg, hi⟩
      exact l.endpoints_lower_ne_gate_middle hl hg hlow hslSide (hport.trans hi)
    have hzero := (canonical_probe_inventory_errors_cancel l p hl hM haxes initial target hgate hpartners hr ha i).2.1 hn
    change Inventory.count (ordinaryAxis p upper.port) t - Inventory.count (ordinaryAxis p upper.port) (I).initial = 0 at hzero
    have hb := canonical_ordinaryAxis_surplus_balance l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hr .refl ha
    change (Inventory.count (ordinaryAxis p upper.port) t - Inventory.count (ordinaryAxis p upper.port) (I).initial) +
      (holes t ∩ ordinaryAxis p upper.port).card = 5 at hb
    simpa only [hzero, Nat.zero_add] using hb
  · intro g hg kind hk
    let i : Fin l.portCount := ⟨g.left + 1, gate_middle_lt l hl (placement_gate_mem l hg hk)⟩
    have hm : Partner.Middle l i.val := ⟨kind, g.left, placement_gate_mem l hg hk, rfl⟩
    have hzero := (canonical_probe_inventory_errors_cancel l p hl hM haxes initial target hgate hpartners hr ha i).2.2 hm
    change Inventory.count (gateAxis p (g.left + 1)) (I).initial - Inventory.count (gateAxis p (g.left + 1)) t = 0 at hzero
    have hb := canonical_gateAxis_deficit_balance l p hl hM haxes initial target hgate hg hk hr .refl ha
    change (holes t ∩ gateAxis p (g.left + 1)).card = 4 +
      (Inventory.count (gateAxis p (g.left + 1)) (I).initial - Inventory.count (gateAxis p (g.left + 1)) t) at hb
    simpa only [hzero, Nat.add_zero] using hb

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

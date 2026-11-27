/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptancePhysicalDynamics
public import Push.AcceptanceGateRelayFailure
public import Push.AcceptanceGateCoreFailure
public import PushS.PortGateTrainUnique

/-! The certified actual terminal rail thresholds exclude relay and AND-left faults along their genuine suffixes. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

/-- A genuine target-threshold rail of a legal target excludes every physical relay fault. -/
private theorem GateRailTerminalReadout.no_relay {p : Scales.Parameters} {g : Placement}
    {kind : Shuttle.Kind}
    {t : State (p.W + 1) (p.H + 1)} {target : Shuttle.Target} {b : ThreeBlocks}
    (readout : GateRailTerminalReadout p g kind t target b) (legal : target.Legal kind)
    {other : ThreeBlocks} (fault : GateRelayFault p g kind t other) : False := by
  have same := fault.shape.unique readout.shape
  rw [same] at fault
  have heavy := readout.heavy.mpr fault.short
  have right := readout.relay.mp (legal.1 heavy)
  have failed := fault.right
  omega

/-- Legal AND target thresholds exclude the physical short-low, left-outward fault. -/
private theorem GateRailTerminalReadout.no_andLeft {p : Scales.Parameters} {g : Placement}
    {t : State (p.W + 1) (p.H + 1)} {target : Shuttle.Target} {b : ThreeBlocks}
    (readout : GateRailTerminalReadout p g .andGate t target b) (legal : target.Legal .andGate)
    {upper : Endpoint} {state : GateCorePlacement} (fault : GateAndLeftFault p g upper t state) : False := by
  have same := fault.readout.rail_shape.unique readout.shape
  have short : (gateTrainPlacement p g b).short ≤ 5 := same ▸ fault.short
  have left : 2 ≤ (gateTrainPlacement p g b).left := same ▸ fault.left
  have heavy : target.heavy = false := by
    cases bit : target.heavy
    · rfl
    · have high := readout.heavy.mp bit
      omega
  have supplied := readout.left.mp (legal.2 rfl heavy)
  omega

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) (hlegal : l.InputLegal target)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hlegal

/-- An actual accepted gate's balanced terminal rail has no relay fault. -/
private theorem canonical_gate_terminal_relay_impossible {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11)
    {b : ThreeBlocks} (fault : GateRelayFault p g kind t b) : False := by
  obtain ⟨b, readout⟩ := canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk
    hr accepted axisInventory railInventory
  exact readout.no_relay (canonicalShuttleTarget_legal l target hlegal hg hk) fault

/-- The corresponding actual balanced terminal AND rail has no AND-left fault. -/
private theorem canonical_gate_terminal_andLeft_impossible {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (I).board none (I).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = Shuttle.Kind.andGate.kappa.toNat + 11)
    {upper : Endpoint} {state : GateCorePlacement} (fault : GateAndLeftFault p g upper t state) : False := by
  obtain ⟨b, readout⟩ := canonical_gateRail_terminal_readout l p hl hM haxes initial target hgate hlegal hg hk
    hr accepted axisInventory railInventory
  exact readout.no_andLeft (canonicalShuttleTarget_legal l target hlegal hg hk) fault

/-- Every real accepted prefix is free of relay faults once its actual terminal inventories are balanced. -/
theorem canonical_gate_relay_fault_impossible_of_inventory {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : AxisInventories l p t) (railInventory : GateRailInventories l p t)
    {b : ThreeBlocks} (fault : GateRelayFault p g kind u b) : False := by
  have dynamics := canonical_physical_dynamics_of_inventory l p hl hM haxes initial target hgate hlegal accepted axisInventory railInventory
  obtain ⟨next, finalFault⟩ := canonical_gate_relay_failure_suffix l p hl hM haxes initial target hg hk hsu hut accepted dynamics.rail fault
  exact canonical_gate_terminal_relay_impossible l p hl hM haxes initial target hgate hlegal hg hk (hsu.trans hut) accepted
    (axisInventory.gate g hg kind hk) (railInventory.gate g hg kind hk) finalFault

/-- Real accepted prefixes also exclude every outside AND-left fault under the same terminal numerical inventories. -/
theorem canonical_gate_andLeft_fault_impossible_of_inventory {g : Placement} (hg : g ∈ placements l)
    (hk : g.gate = some .andGate) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : AxisInventories l p t) (railInventory : GateRailInventories l p t)
    {state : GateCorePlacement} (fault : GateAndLeftFault p g upper u state) : False := by
  have dynamics := canonical_physical_dynamics_of_inventory l p hl hM haxes initial target hgate hlegal accepted axisInventory railInventory
  obtain ⟨next, finalFault⟩ := canonical_gate_and_left_failure_suffix_of_dynamics l p hl hM haxes initial target hgate
    hg hk hu hs hp hsu hut accepted dynamics fault
  exact canonical_gate_terminal_andLeft_impossible l p hl hM haxes initial target hgate hlegal hg hk (hsu.trans hut) accepted
    (axisInventory.gate g hg .andGate hk) (railInventory.gate g hg .andGate hk) finalFault

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

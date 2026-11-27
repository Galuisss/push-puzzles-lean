/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisTerminalReadout
public import Push.AcceptanceGateAxisTerminalReadout
public import Push.AcceptanceAxisReadoutFromTerminal
public import Push.AcceptanceGateAxisReadoutFromTerminal
public import Push.AcceptanceDecodedInputs
import all PushS.PortAxisGroups

/-! Balanced actual terminal axis inventories restore the complete physical axis readouts and motions. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram AcceptanceAxisReadout

/-- The original ordinary and gate-middle hole inventories at one actual endpoint. -/
structure AxisInventories (l : PortLayout) (p : Scales.Parameters)
    (t : State (p.W + 1) (p.H + 1)) : Prop where
  ordinary : ∀ upper lower, upper ∈ l.endpoints → lower ∈ l.endpoints →
    upper.side = .upper → lower.side = .lower → lower.port = upper.port →
      (holes t ∩ ordinaryAxis p upper.port).card = 5
  gate : ∀ g, g ∈ placements l → ∀ kind, g.gate = some kind →
    (holes t ∩ gateAxis p (g.left + 1)).card = 4

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- The actual ordinary words at every prefix follow from the terminal numerical inventories. -/
private theorem canonical_shared_axis_readouts_of_inventory {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : AcceptanceDecodedInputs.SharedAxisReadouts l p u := by
  constructor
  intro upper lower hu hlow hsuSide hslSide hport
  obtain ⟨a, word, _, _⟩ := canonical_ordinaryAxis_terminal_readout l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport (hsu.trans hut) accepted
    (inventory.ordinary upper lower hu hlow hsuSide hslSide hport)
  exact canonical_ordinaryAxis_readout_of_terminal_word l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu hut accepted word

/-- Every real gate-middle word also follows from its terminal four-hole inventory. -/
theorem canonical_gate_axis_readout_of_inventory {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hport : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : ∃ a, GateAxisReadout p g upper u a := by
  obtain ⟨a, word, _⟩ := canonical_gateAxis_terminal_readout l p hl hM haxes initial target hgate
    hg hk hu hsuSide hport (hsu.trans hut) accepted (inventory.gate g hg kind hk)
  exact canonical_gateAxis_readout_of_terminal_word l p hl hM haxes initial target hgate
    hg hk hu hsuSide hport hsu hut accepted word

/-- The actual balanced source trace carries all shared train motions on every physical step. -/
theorem canonical_axis_motions_of_inventory {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : AxisMotions l p u v := by
  constructor
  · intro upper lower hu hlow hsuSide hslSide hport
    obtain ⟨a, word, _, _⟩ := canonical_ordinaryAxis_terminal_readout l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport ((hsu.tail step).trans hvt) accepted
      (inventory.ordinary upper lower hu hlow hsuSide hslSide hport)
    exact canonical_ordinaryAxis_motion_of_terminal_word l p hl hM haxes initial target hgate
      hu hlow hsuSide hslSide hport hsu step hvt accepted word
  · intro g hg kind hk upper hu hsuSide hport
    obtain ⟨a, word, _⟩ := canonical_gateAxis_terminal_readout l p hl hM haxes initial target hgate
      hg hk hu hsuSide hport ((hsu.tail step).trans hvt) accepted (inventory.gate g hg kind hk)
    exact canonical_gateAxis_motion_of_terminal_word l p hl hM haxes initial target hgate
      hg hk hu hsuSide hport hsu step hvt accepted word

/-- Every actual endpoint has its genuine half-axis word throughout a balanced accepted trace. -/
theorem canonical_endpoint_axis_readout_of_inventory (e : Endpoint) (he : e ∈ l.endpoints)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
  have shared := canonical_shared_axis_readouts_of_inventory l p hl hM haxes initial target hgate hsu hut accepted inventory
  cases hs : e.side with
  | lower => exact shared.lower_exists hl he hs
  | upper =>
    obtain ⟨groups⟩ := l.axisGroups_nonempty hl (l.endpoints_port_lt hl he)
    have outer (hk : e.port = groups.lower.left ∨ e.port = groups.lower.right) :
        ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
      obtain ⟨lower, hlow, hls, hlp, _⟩ := placement_outer_endpoint l groups.lower_mem hk
      obtain ⟨a, word⟩ := shared.ordinary e lower he hlow hs (hls.trans groups.lower_side) hlp
      exact ⟨a.parameter, a.upperShift, word.upper_endpoint hs⟩
    rcases groups.lower_port with hleft | hright | ⟨gate, middle⟩
    · exact outer (Or.inl hleft)
    · exact outer (Or.inr hright)
    · cases hk : groups.lower.gate with
      | none => simp only [hk, Option.isSome_none, Bool.false_eq_true] at gate
      | some kind =>
        obtain ⟨a, word⟩ := canonical_gate_axis_readout_of_inventory l p hl hM haxes initial target hgate
          groups.lower_mem hk he hs middle hsu hut accepted inventory
        exact ⟨a.parameter, a.upperShift, word.upper_endpoint hs middle⟩

/-- The same true numerical inventories supply a complete original Boolean axis array at each prefix. -/
theorem canonical_axis_readout_exists_of_inventory {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : AxisInventories l p t) : ∃ axes, l.AxisReadout p u axes := by
  apply axisReadout_exists_of_endpoint_words l p hl hM haxes
  intro e he _
  exact canonical_endpoint_axis_readout_of_inventory l p hl hM haxes initial target hgate e he hsu hut accepted inventory

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

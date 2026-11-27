/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceDecodedInputsMotions
public import Push.AcceptanceGateCoreMotion
public import Push.AcceptanceGateLegalStep
public import PushS.PortInputGroups
import all PushS.PortWireIndexing
import all PushS.PortGateIndexing
import all PushS.PortSegments

/-! Actual axis and rail motions preserve decoded native input legality when physical target faults are excluded. -/

public section
namespace PushPuzzle.Push.AcceptanceDecodedInputs

open PushFS PushS PushS.PortLayout AcceptanceAxisReadout

private theorem supplied_of_no_fault {p : Scales.Parameters} {e : Endpoint}
    {v : State (p.W + 1) (p.H + 1)} {parameter shift horizontal : ℕ}
    (axis : EndpointAxisReadout p e v parameter shift) (rail : EndpointHorizontalReadout p e v horizontal)
    (excluded : ¬Nonempty (OrdinaryFaultReadout p e v)) : parameter ≤ 1 ∨ 2 ≤ horizontal := by
  by_cases supplied : parameter ≤ 1
  · exact Or.inl supplied
  · right
    by_contra failed
    exact excluded ⟨⟨parameter, shift, horizontal, axis, by omega, rail, by omega⟩⟩

private theorem wire_target_inputs (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (axis : AxisMotions l p u v) (rails : RailMotions l p B u v)
    {next : List Bool} (target : l.AxisReadout p v next)
    (ordinaryNoFault : ∀ e ∈ l.endpoints, ¬Nonempty (OrdinaryFaultReadout p e v))
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    if g.side = .upper then next.getD g.left false = true ∨ next.getD g.right false = true
    else next.getD g.left false = false ∨ next.getD g.right false = false := by
  obtain ⟨motion⟩ := rails.wire g hg hw
  have rail := motion.target_shape.readout motion.marked.length_pos
  have endpoints := wire_endpoints l hg hw
  obtain ⟨left, ls, leftWord⟩ := axis.after_shared.endpoint_exists hl target _ endpoints.1
  obtain ⟨right, rs, rightWord⟩ := axis.after_shared.endpoint_exists hl target _ endpoints.2
  have leftSupply := supplied_of_no_fault leftWord (rail.left_endpoint hl hg hw) (ordinaryNoFault _ endpoints.1)
  have rightSupply := supplied_of_no_fault rightWord (rail.right_endpoint hl hg hw) (ordinaryNoFault _ endpoints.2)
  exact decoded_wire_inputs l p hl hM haxes axis.after_shared hg hw target rail leftWord rightWord leftSupply rightSupply

private theorem gate_target_inputs (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : Step B none u v) (axis : AxisMotions l p u v) (rails : RailMotions l p B u v)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes)
    (gateNoFault : ∀ g ∈ placements l, ∀ kind, g.gate = some kind →
      ∀ upper ∈ l.endpoints, upper.side = .upper → upper.port = g.left + 1 → GateFaultExclusions p g kind upper v)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    if kind = .andGate then next.getD g.right false = false ∨
      (next.getD g.left false = false ∧ next.getD (g.left + 1) false = false)
    else next.getD g.left false = false ∨ next.getD (g.left + 1) false = false ∨ next.getD g.right false = false := by
  have ports := gate_port_bounds l hl hg hk
  have shape := placement_gate_shape l hg hk
  have middle : g.left + 1 < l.portCount := by omega
  obtain ⟨upper, hu, hs, hp⟩ := l.endpoints_upper_exists hl middle
  obtain ⟨before, readout⟩ := gate_group_readout_before l p hl axis rails hg hk hu hs hp
  have beforeLegal := (decoded_gate_inputs_iff l p hl hM haxes axis.before_shared hg hk hu hs hp source readout).mpr
    (hsource.gate_inputs hg hk)
  obtain ⟨core, motion⟩ := gate_core_step_of_motions l p hl hM haxes axis rails hg hk hu hs hp readout.core
  have endpoints := gate_endpoints l hg hk
  obtain ⟨left, ls, leftWord⟩ := axis.after_shared.lower_exists hl endpoints.1 shape.1
  obtain ⟨right, rs, rightWord⟩ := axis.after_shared.lower_exists hl endpoints.2 shape.1
  let after : GateGroupPlacement := ⟨core, left, right, ls, rs⟩
  have afterReadout : GateGroupReadout p g kind upper v after := ⟨motion.after_readout, leftWord, rightWord⟩
  have afterLegal := gate_group_legal_step_of_faults l p hl hM haxes axis hg hk hu hs hp readout afterReadout
    beforeLegal (gateNoFault g hg kind hk upper hu hs hp) (players_adjacent step.choose_spec)
  exact (decoded_gate_inputs_iff l p hl hM haxes axis.after_shared hg hk hu hs hp target afterReadout).mp afterLegal

/-- A true physical step with complete train motions and target fault exclusions preserves decoded native input legality. -/
theorem decoded_legal_step_of_motions (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : Step B none u v) (axis : AxisMotions l p u v) (rails : RailMotions l p B u v)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes)
    (ordinaryNoFault : ∀ e ∈ l.endpoints, ¬Nonempty (OrdinaryFaultReadout p e v))
    (gateNoFault : ∀ g ∈ placements l, ∀ kind, g.gate = some kind →
      ∀ upper ∈ l.endpoints, upper.side = .upper → upper.port = g.left + 1 → GateFaultExclusions p g kind upper v) :
    l.InputLegal next := by
  exact InputLegal.of_placements l next target.axes_length
    (fun _ hg hw => wire_target_inputs l p hl hM haxes axis rails target ordinaryNoFault hg hw)
    (fun _ hg _ hk => gate_target_inputs l p hl hM haxes step axis rails source target hsource gateNoFault hg hk)

/-- Under the same actual target fault exclusions, the decoded physical step stutters or reverses one legal original axis. -/
theorem decoded_axis_step_of_faults (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : Step B none u v) (axis : AxisMotions l p u v) (rails : RailMotions l p B u v)
    {axes next : List Bool} (source : l.AxisReadout p u axes) (target : l.AxisReadout p v next)
    (hsource : l.InputLegal axes)
    (ordinaryNoFault : ∀ e ∈ l.endpoints, ¬Nonempty (OrdinaryFaultReadout p e v))
    (gateNoFault : ∀ g ∈ placements l, ∀ kind, g.gate = some kind →
      ∀ upper ∈ l.endpoints, upper.side = .upper → upper.port = g.left + 1 → GateFaultExclusions p g kind upper v) :
    axes = next ∨ l.AxisStep axes next :=
  axisReadout_step_of_motions l p hl axis source target hsource
    (decoded_legal_step_of_motions l p hl hM haxes step axis rails source target hsource ordinaryNoFault gateNoFault)

end PushPuzzle.Push.AcceptanceDecodedInputs

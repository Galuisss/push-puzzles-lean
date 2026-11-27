/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortAxisDecode
public import PushS.PortGateGroupReadout
public import PushS.PortWireTrainReadout
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing

/-! Decoding actual lower, gate and WIRE inputs from shared physical words and endpoint supplies. -/

public section
namespace PushPuzzle.Push.AcceptanceDecodedInputs

open PushFS PushS PushS.PortLayout

/-- The actual joint ordinary readout of every upper/lower endpoint pair sharing one original port. -/
structure SharedAxisReadouts (l : PortLayout) (p : Scales.Parameters)
    (u : State (p.W + 1) (p.H + 1)) : Prop where
  ordinary : ∀ upper lower, upper ∈ l.endpoints → lower ∈ l.endpoints →
    upper.side = .upper → lower.side = .lower → lower.port = upper.port →
      ∃ placement, OrdinaryAxisReadout p upper lower u placement

/-- Every lower ordinary endpoint has its actual word in the corresponding genuine shared-axis readout. -/
theorem SharedAxisReadouts.lower_exists {l : PortLayout} {p : Scales.Parameters}
    (hl : l.pages.Valid) {u : State (p.W + 1) (p.H + 1)} (shared : SharedAxisReadouts l p u)
    {lower : Endpoint} (hlow : lower ∈ l.endpoints) (hsl : lower.side = .lower) :
    ∃ parameter shift, EndpointAxisReadout p lower u parameter shift := by
  obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl hlow)
  obtain ⟨placement, joint⟩ := shared.ordinary upper lower hu hlow hsu hsl hp.symm
  exact ⟨placement.lowerParameter, placement.lowerShift, joint.lower_endpoint hsl hp.symm⟩

/-- The decoded upper words and shared lower words cover every actual ordinary endpoint. -/
theorem SharedAxisReadouts.endpoint_exists {l : PortLayout} {p : Scales.Parameters}
    (hl : l.pages.Valid) {u : State (p.W + 1) (p.H + 1)} (shared : SharedAxisReadouts l p u)
    {axes : List Bool} (decoded : l.AxisReadout p u axes) (e : Endpoint) (he : e ∈ l.endpoints) :
    ∃ parameter shift, EndpointAxisReadout p e u parameter shift := by
  cases hs : e.side
  · exact decoded.upper_exists e he hs
  · exact shared.lower_exists hl he hs

/-- An actual lower ordinary endpoint receives the false threshold of the same decoded shared axis. -/
theorem decoded_lower (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {u : State (p.W + 1) (p.H + 1)} (shared : SharedAxisReadouts l p u)
    {axes : List Bool} (decoded : l.AxisReadout p u axes)
    {lower : Endpoint} (hlow : lower ∈ l.endpoints) (hsl : lower.side = .lower)
    {parameter shift : ℕ} (word : EndpointAxisReadout p lower u parameter shift) :
    parameter ≤ 1 ↔ axes.getD lower.port false = false := by
  obtain ⟨upper, hu, hsu, hp⟩ := l.endpoints_upper_exists hl (l.endpoints_port_lt hl hlow)
  obtain ⟨placement, joint⟩ := shared.ordinary upper lower hu hlow hsu hsl hp.symm
  exact decoded.lower_false_iff hl hM haxes hu hlow hsu hsl hp.symm joint word

/-- The genuine same-gate threshold is exactly the three Boolean inputs of its original metadata. -/
theorem decoded_gate_inputs_iff (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {u : State (p.W + 1) (p.H + 1)} (shared : SharedAxisReadouts l p u)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {axes : List Bool} (decoded : l.AxisReadout p u axes)
    {state : GateGroupPlacement} (readout : GateGroupReadout p g kind upper u state) :
    state.external.Legal kind ↔
      if kind = .andGate then axes.getD g.right false = false ∨
        (axes.getD g.left false = false ∧ axes.getD (g.left + 1) false = false)
      else axes.getD g.left false = false ∨ axes.getD (g.left + 1) false = false ∨
        axes.getD g.right false = false := by
  have he := PortLayout.gate_endpoints l hg hk
  have hside := (PortLayout.placement_gate_shape l hg hk).1
  have hL := decoded_lower l p hl hM haxes shared decoded he.1 hside readout.left_axis
  have hR := decoded_lower l p hl hM haxes shared decoded he.2 hside readout.right_axis
  have hC := decoded.gate_middle_false_iff hu hsu hp readout.core.axis_readout
  change state.leftParameter ≤ 1 ↔ axes.getD g.left false = false at hL
  change state.rightParameter ≤ 1 ↔ axes.getD g.right false = false at hR
  cases kind <;> simp only [Shuttle.External.Legal, GateGroupPlacement.external, reduceCtorEq, ite_true, ite_false]
  · rw [hL, hR, hC]
  · rw [hL, hR, hC]

/-- A real WIRE rail with both actual endpoint supplies gives one of its two decoded input bits. -/
theorem decoded_wire_inputs (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {u : State (p.W + 1) (p.H + 1)} (shared : SharedAxisReadouts l p u)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {axes : List Bool} (decoded : l.AxisReadout p u axes)
    {left right leftParameter leftShift rightParameter rightShift : ℕ}
    (rail : WireRailReadout p g u left right)
    (leftWord : EndpointAxisReadout p ⟨g.side, g.left, true, g.level, g.internal⟩ u leftParameter leftShift)
    (rightWord : EndpointAxisReadout p ⟨g.side, g.right, false, g.level, g.internal⟩ u rightParameter rightShift)
    (leftSupplied : leftParameter ≤ 1 ∨ 2 ≤ left) (rightSupplied : rightParameter ≤ 1 ∨ 2 ≤ right) :
    if g.side = .upper then axes.getD g.left false = true ∨ axes.getD g.right false = true
    else axes.getD g.left false = false ∨ axes.getD g.right false = false := by
  have he := PortLayout.wire_endpoints l hg hw
  have hsum := rail.holes_sum
  have hinput : leftParameter ≤ 1 ∨ rightParameter ≤ 1 := by omega
  cases hs : g.side with
  | upper =>
    simp only [ite_true]
    rcases hinput with h | h
    · exact Or.inl ((decoded.upper _ he.1 hs leftWord).mpr h)
    · exact Or.inr ((decoded.upper _ he.2 hs rightWord).mpr h)
  | lower =>
    simp only [reduceCtorEq, ite_false]
    exact hinput.imp
      (decoded_lower l p hl hM haxes shared decoded he.1 hs leftWord).mp
      (decoded_lower l p hl hM haxes shared decoded he.2 hs rightWord).mp

end PushPuzzle.Push.AcceptanceDecodedInputs

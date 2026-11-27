/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisDecode
public import PushS.PortGateGroupLegalStep
public import PushS.PortInputGroups
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing

/-! Actual successful readouts give all ordinary WIRE thresholds and decode the native gate thresholds exactly. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

section Readout
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The same actual gate threshold is exactly its original three decoded Boolean inputs. -/
theorem physicalInstance_decoded_gate_inputs_iff {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {axes : List Bool} (decoded : l.AxisReadout p u axes)
    {state : GateGroupPlacement} (readout : GateGroupReadout p g kind upper u state) :
    state.external.Legal kind ↔
      if kind = .andGate then axes.getD g.right false = false ∨
        (axes.getD g.left false = false ∧ axes.getD (g.left + 1) false = false)
      else axes.getD g.left false = false ∨ axes.getD (g.left + 1) false = false ∨ axes.getD g.right false = false := by
  have he := gate_endpoints l hg hk
  have hside := (placement_gate_shape l hg hk).1
  have hL := l.physicalInstance_decoded_lower p hl hM ha initial target hsu hut ht decoded he.1 hside readout.left_axis
  have hR := l.physicalInstance_decoded_lower p hl hM ha initial target hsu hut ht decoded he.2 hside readout.right_axis
  have hC := decoded.gate_middle_false_iff hu hsuSide hp readout.core.axis_readout
  change state.leftParameter ≤ 1 ↔ axes.getD g.left false = false at hL
  change state.rightParameter ≤ 1 ↔ axes.getD g.right false = false at hR
  cases kind <;> simp only [Shuttle.External.Legal, GateGroupPlacement.external, reduceCtorEq, ite_true, ite_false]
  · rw [hL, hR, hC]
  · rw [hL, hR, hC]

end Readout

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial : SignalState)
  (targetAxes : List Bool) (hlegal : l.InputLegal targetAxes)

local notation "I" => l.physicalInstance p hl hM ha initial (l.canonical targetAxes)

include hlegal

/-- Every actual ordinary WIRE receives one of its two original decoded page inputs on every successful prefix. -/
theorem physicalInstance_decoded_wire_inputs {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) {axes : List Bool} (decoded : l.AxisReadout p u axes) :
    if g.side = .upper then axes.getD g.left false = true ∨ axes.getD g.right false = true
    else axes.getD g.left false = false ∨ axes.getD g.right false = false := by
  have he := wire_endpoints l hg hw
  obtain ⟨left, right, horizontal⟩ := l.physicalInstance_wire_train_readout p hl hM ha initial (l.canonical targetAxes) hg hw hsu hut ht
  obtain ⟨lt, ls, leftWord⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial (l.canonical targetAxes) _ he.1 hsu hut ht
  obtain ⟨rt, rs, rightWord⟩ := l.physicalInstance_endpoint_axis_readout p hl hM ha initial (l.canonical targetAxes) _ he.2 hsu hut ht
  have hlSup := l.physicalInstance_ordinary_endpoint_supplied p hl hM ha initial targetAxes hlegal _ he.1 hsu hut ht
    leftWord (horizontal.left_endpoint hl hg hw)
  have hrSup := l.physicalInstance_ordinary_endpoint_supplied p hl hM ha initial targetAxes hlegal _ he.2 hsu hut ht
    rightWord (horizontal.right_endpoint hl hg hw)
  have hsum := horizontal.holes_sum
  have hinput : lt ≤ 1 ∨ rt ≤ 1 := by omega
  cases hs : g.side with
  | upper =>
    simp only [ite_true]
    rcases hinput with h | h
    · exact Or.inl ((decoded.upper _ he.1 hs leftWord).mpr h)
    · exact Or.inr ((decoded.upper _ he.2 hs rightWord).mpr h)
  | lower =>
    simp only [reduceCtorEq, ite_false]
    have hL := l.physicalInstance_decoded_lower p hl hM ha initial (l.canonical targetAxes) hsu hut ht decoded he.1 hs leftWord
    have hR := l.physicalInstance_decoded_lower p hl hM ha initial (l.canonical targetAxes) hsu hut ht decoded he.2 hs rightWord
    exact hinput.imp hL.mp hR.mp

end Canonical
end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisReadoutMotion
import all PushS.PortAxisTrainReadout
import all PushS.PortAxisTrainStep
import all PushS.PortGateAxisTrainReadout

/-! Actual marked train steps give shared-axis motions on arbitrary boards. -/

public section
namespace PushPuzzle.Push.AcceptanceAxisReadout

open PushFS PushS PushS.PortLayout PushS.RowLabels

/-- A genuine gapped ordinary train layout supplies its complete complementary endpoint words. -/
theorem ordinary_readout_of_shape {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : ThreeBlocks}
    (shape : OrdinaryAxisTrainShape p upper lower u b) (positive : b.Positive) :
    OrdinaryAxisReadout p upper lower u (ordinaryAxisPlacement p upper b) :=
  shape.readout positive

/-- A genuine gapped gate train layout supplies its upper endpoint and middle words. -/
theorem gate_readout_of_shape {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {b : TwoBlocks}
    (shape : GateAxisTrainShape p g upper u b) (positive : b.Positive) :
    GateAxisReadout p g upper u (gateAxisPlacement p upper b) :=
  shape.readout positive

/-- An actual marked ordinary-axis step gives both physical readouts and forcing coordinates. -/
theorem ordinary_motion_of_markedStep (p : Scales.Parameters) (upper lower : Endpoint)
    (initial : SignalState) (positive : (ordinaryAxisTrainBlocks p upper lower initial).Positive)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : ThreeBlocks.MarkedStep (ordinaryAxisTrainBlocks p upper lower initial) positive B none
      .south (p.x upper.port) (BoxMask.keep u (ordinaryAxis p upper.port)) (BoxMask.keep v (ordinaryAxis p upper.port))) :
    OrdinaryAxisMotion p upper lower u v step.beforeBlocks step.afterBlocks := by
  have before := shape_of_line (p := p) (upper := upper) (lower := lower) initial positive step.before u
    step.before_state step.before_gapped step.before_slots
  have after := shape_of_line (p := p) (upper := upper) (lower := lower) initial positive step.after v
    step.after_state step.after_gapped step.after_slots
  refine ⟨before, after, ordinary_readout_of_shape before positive,
    ordinary_readout_of_shape after positive, ?_, ?_, step.middle_forward, step.middle_backward⟩
  · intro changed
    exact step.player_lane (Or.inr (Or.inl changed))
  · exact step.step.coordinate_bounds ⟨(ordinaryAxisTrainBlocks p upper lower initial).firstLength, by
      dsimp only [ThreeBlocks.size]
      have h := positive.2.1
      omega⟩

private theorem gate_shape_of_line (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (initial : SignalState) (positive : (gateAxisTrainBlocks p upper initial).Positive)
    (line : LineState (Fin (gateAxisTrainBlocks p upper initial).size)
      (p.W + 1) (p.H + 1) .south (p.x (g.left + 1)))
    (u : State (p.W + 1) (p.H + 1))
    (state : line.state = BoxMask.keep u (gateAxis p (g.left + 1)))
    (gapped : ((gateAxisTrainBlocks p upper initial).atState positive line).Gapped)
    (slots : (lineBoxes .south (p.x (g.left + 1)) line.state).image Direction.south.position =
      ((gateAxisTrainBlocks p upper initial).atState positive line).slots) :
    GateAxisTrainShape p g upper u ((gateAxisTrainBlocks p upper initial).atState positive line) := by
  refine ⟨rfl, rfl, gapped, ?_⟩
  rw [state, BoxMask.lineBoxes_keep] at slots
  · exact slots
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

/-- An actual marked gate-axis step gives both physical layouts and all forcing coordinates. -/
theorem gate_motion_of_markedStep (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (initial : SignalState) (positive : (gateAxisTrainBlocks p upper initial).Positive)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : TwoBlocks.MarkedStep (gateAxisTrainBlocks p upper initial) positive B none
      .south (p.x (g.left + 1)) (BoxMask.keep u (gateAxis p (g.left + 1))) (BoxMask.keep v (gateAxis p (g.left + 1)))) :
    GateAxisTrainMotion p g upper u v step.beforeBlocks step.afterBlocks := by
  refine ⟨gate_shape_of_line p g upper initial positive step.before u step.before_state step.before_gapped step.before_slots,
    gate_shape_of_line p g upper initial positive step.after v step.after_state step.after_gapped step.after_slots,
    positive, positive, step.player_lane, ?_, ?_, step.first_forward, step.first_backward, step.last_forward, step.last_backward⟩
  · exact step.step.coordinate_bounds ⟨0, by dsimp only [TwoBlocks.size]; have h := positive.1; omega⟩
  · exact step.step.coordinate_bounds ⟨(gateAxisTrainBlocks p upper initial).firstLength, by
      dsimp only [TwoBlocks.size]; have h := positive.2; omega⟩

end PushPuzzle.Push.AcceptanceAxisReadout

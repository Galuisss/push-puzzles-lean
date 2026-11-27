/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortGateTrainStep
public import PushS.PortWireTrainStep
import all PushS.PortGateTrainStep
import all PushS.PortWireTrains

/-! Gate and WIRE train motion from genuine masked line steps on arbitrary boards. -/

public section
namespace PushPuzzle.Push.AcceptanceRailReadout

open PushFS PushS PushS.PortLayout PushS.RowLabels

/-- An actual marked canonical gate-rail step gives all three train motions and player forcing coordinates. -/
theorem gate_rail_motion_of_markedStep (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (initial : SignalState) (positive : (gateTrainBlocks p g kind initial).Positive)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)}
    (step : ThreeBlocks.MarkedStep (gateTrainBlocks p g kind initial) positive B none .east
      (p.H - readDepth p 1) (BoxMask.keep u (gateOpenRail p g)) (BoxMask.keep v (gateOpenRail p g))) :
    GateTrainMotion p g kind u v step.beforeBlocks step.afterBlocks := by
  refine ⟨PortLayout.shape_of_line p g kind initial positive step.before u step.before_state
      step.before_gapped step.before_slots,
    PortLayout.shape_of_line p g kind initial positive step.after v step.after_state
      step.after_gapped step.after_slots,
    step.player_lane, ?_, ?_, ?_, step.first_forward, step.first_backward,
      step.middle_forward, step.middle_backward, step.last_forward, step.last_backward⟩
  · exact step.step.coordinate_bounds ⟨0, by
      dsimp only [ThreeBlocks.size]
      have h := positive.1
      omega⟩
  · exact step.step.coordinate_bounds ⟨(gateTrainBlocks p g kind initial).firstLength, by
      dsimp only [ThreeBlocks.size]
      have h := positive.2.1
      omega⟩
  · exact step.step.coordinate_bounds ⟨(gateTrainBlocks p g kind initial).firstLength +
      (gateTrainBlocks p g kind initial).middleLength, by
      dsimp only [ThreeBlocks.size]
      have h := positive.2.2
      omega⟩

/-- Two genuine full WIRE interval layouts lift their masked physical step with the complete original train marks. -/
theorem wire_train_step_of_shapes (p : Scales.Parameters) (g : Placement)
    {B : Board (p.W + 1) (p.H + 1)} {u v : State (p.W + 1) (p.H + 1)} {first next : ℤ}
    (positive : 0 < wireTrainLength p g)
    (before : WireTrainShape p g u first) (after : WireTrainShape p g v next)
    (step : LineAdmissible B none .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep u (wireOpenRail p g)) (BoxMask.keep v (wireOpenRail p g))) :
    Nonempty (WireTrainStep p g B u v) := by
  have hon (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ wireOpenRail p g) :
      Direction.east.lane q = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level :=
    (Finset.mem_filter.mp hq).2.1
  have sourceSlots : (lineBoxes .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep u (wireOpenRail p g))).image Direction.east.position =
      Finset.Ico first (first + wireTrainLength p g) := by
    rw [BoxMask.lineBoxes_keep hon]
    exact before.slots
  have targetSlots : (lineBoxes .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep v (wireOpenRail p g))).image Direction.east.position =
      Finset.Ico next (next + wireTrainLength p g) := by
    rw [BoxMask.lineBoxes_keep hon]
    exact after.slots
  obtain ⟨marked⟩ := interval_marked_step positive step sourceSlots targetSlots
  exact ⟨⟨first, next, before, after, marked⟩⟩

end PushPuzzle.Push.AcceptanceRailReadout

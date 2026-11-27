/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTrainReadout
public import PushS.TrainStep

/-! Actual complete-board gate train motion and the exact gap required for each displacement. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- One native gate-rail step with its two rigid layouts and all actual forcing coordinates. -/
structure GateTrainMotion (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (u v : State (p.W + 1) (p.H + 1)) (before after : ThreeBlocks) : Prop where
  before_shape : GateTrainShape p g kind u before
  after_shape : GateTrainShape p g kind v after
  player_row (changed : before.first ≠ after.first ∨ before.middle ≠ after.middle ∨ before.last ≠ after.last) :
    u.player.2.val = p.H - readDepth p 1
  first_bounds : before.first - 1 ≤ after.first ∧ after.first ≤ before.first + 1
  middle_bounds : before.middle - 1 ≤ after.middle ∧ after.middle ≤ before.middle + 1
  last_bounds : before.last - 1 ≤ after.last ∧ after.last ≤ before.last + 1
  first_forward (moved : before.first < after.first) : (u.player.1.val : ℤ) = before.first - 1
  first_backward (moved : after.first < before.first) : (u.player.1.val : ℤ) = before.first + before.firstLength
  middle_forward (moved : before.middle < after.middle) : (u.player.1.val : ℤ) = before.middle - 1
  middle_backward (moved : after.middle < before.middle) : (u.player.1.val : ℤ) = before.middle + before.middleLength
  last_forward (moved : before.last < after.last) : (u.player.1.val : ℤ) = before.last - 1
  last_backward (moved : after.last < before.last) : (u.player.1.val : ℤ) = before.last + before.lastLength

private theorem shape_of_line (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (initial : SignalState) (hpos : (gateTrainBlocks p g kind initial).Positive)
    (T : LineState (Fin (gateTrainBlocks p g kind initial).size) (p.W + 1) (p.H + 1) .east (p.H - readDepth p 1))
    (s : State (p.W + 1) (p.H + 1)) (hstate : T.state = BoxMask.keep s (gateOpenRail p g))
    (hgap : ((gateTrainBlocks p g kind initial).atState hpos T).Gapped)
    (hs : (lineBoxes .east (p.H - readDepth p 1) T.state).image Direction.east.position =
      ((gateTrainBlocks p g kind initial).atState hpos T).slots) :
    GateTrainShape p g kind s ((gateTrainBlocks p g kind initial).atState hpos T) := by
  refine ⟨rfl, rfl, rfl, hgap, ?_⟩
  rw [hstate, BoxMask.lineBoxes_keep] at hs
  · exact hs
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- One successful actual gate step lifts with the same original occupancy marks on both sides. -/
theorem physicalInstance_gate_train_marked_step {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    Nonempty (ThreeBlocks.MarkedStep (gateTrainBlocks p g kind initial) (gateTrainBlocks_positive p g kind initial)
      (I).board none .east (p.H - readDepth p 1) (BoxMask.keep u (gateOpenRail p g)) (BoxMask.keep v (gateOpenRail p g))) := by
  let b := gateTrainBlocks p g kind initial
  let c := gateTrainBlocks p g kind target
  have hpre := l.physicalInstance_gateRail_admissible_prefix p hl hM ha initial target hg hk hsu
    ((Relation.ReflTransGen.single hm).trans hvt) ht
  have hpost := l.physicalInstance_gateRail_admissible_suffix p hl hM ha initial target hg hk (hsu.tail hm) hvt ht
  have hstep := BoxMask.keep_admissible (axis := .east) (lane := p.H - readDepth p 1) (gateOpenRail_runClosed p g)
    (fun _ hq => (Finset.mem_filter.mp hq).2.1) hm
    (l.physicalInstance_gateRail_inventory_step p hl hM ha initial target hg hk hsu hm hvt ht)
  exact b.admissible_step (gateTrainBlocks_positive p g kind initial) (gateTrainBlocks_gapped p g kind initial)
    c.first c.middle c.last (gateTrainBlocks_gapped p g kind target) hpre hstep hpost
    (l.physicalInstance_gate_train_initial_slots p hl hM ha initial target hg hk)
    (l.physicalInstance_gate_train_target_slots p hl hM ha initial target hg hk ht)

/-- Every successful actual gate step has rigid train motion and the genuine player position needed for it. -/
theorem physicalInstance_gate_train_motion {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hm : Step (I).board none u v)
    (hvt : Reachable (I).board none v t) (ht : t.boxes = (I).board.goals) :
    ∃ before after, GateTrainMotion p g kind u v before after := by
  obtain ⟨m⟩ := l.physicalInstance_gate_train_marked_step p hl hM ha initial target hg hk hsu hm hvt ht
  refine ⟨m.beforeBlocks, m.afterBlocks,
    shape_of_line p g kind initial _ m.before u m.before_state m.before_gapped m.before_slots,
    shape_of_line p g kind initial _ m.after v m.after_state m.after_gapped m.after_slots,
    m.player_lane, ?_, ?_, ?_, m.first_forward, m.first_backward,
    m.middle_forward, m.middle_backward, m.last_forward, m.last_backward⟩
  · exact m.step.coordinate_bounds ⟨0, by dsimp only [ThreeBlocks.size]; have h := (gateTrainBlocks_positive p g kind initial).1; omega⟩
  · exact m.step.coordinate_bounds ⟨(gateTrainBlocks p g kind initial).firstLength, by
      dsimp only [ThreeBlocks.size]; have h := (gateTrainBlocks_positive p g kind initial).2.1; omega⟩
  · exact m.step.coordinate_bounds ⟨(gateTrainBlocks p g kind initial).firstLength + (gateTrainBlocks p g kind initial).middleLength, by
      dsimp only [ThreeBlocks.size]; have h := (gateTrainBlocks_positive p g kind initial).2.2; omega⟩

end Solution
end PushPuzzle.PushS.PortLayout

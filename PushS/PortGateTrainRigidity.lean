/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTrains
public import PushS.TrainDynamics

/-! Native successful physical trajectories preserve the three gate trains and both internal gaps. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The three physical gate trains have their prescribed lengths and two nonempty internal gaps. -/
structure GateTrainShape (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (u : State (p.W + 1) (p.H + 1)) (blocks : ThreeBlocks) : Prop where
  first_length : blocks.firstLength = p.D - kind.kappa.toNat
  middle_length : blocks.middleLength = 2
  last_length : blocks.lastLength = p.D - 14
  gapped : blocks.Gapped
  slots : (u.boxes ∩ gateOpenRail p g).image Direction.east.position = blocks.slots

/-- Every successful actual gate-rail prefix consists of the original three rigid, unmerged box trains. -/
theorem physicalInstance_gate_train_shape (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ blocks, GateTrainShape p g kind u blocks := by
  let b := gateTrainBlocks p g kind initial
  let c := gateTrainBlocks p g kind target
  have hb := gateTrainBlocks_gapped p g kind initial
  have hc := gateTrainBlocks_gapped p g kind target
  have hpos := gateTrainBlocks_positive p g kind initial
  have hslots := l.physicalInstance_gate_train_initial_slots p hl hM ha initial target hg hk
  have htSlots := l.physicalInstance_gate_train_target_slots p hl hM ha initial target hg hk ht
  have hpre := l.physicalInstance_gateRail_admissible_prefix p hl hM ha initial target hg hk hsu hut ht
  have hpost := l.physicalInstance_gateRail_admissible_suffix p hl hM ha initial target hg hk hsu hut ht
  obtain ⟨blocks, hcopy, hrail⟩ := b.admissible_at hpos hb c.first c.middle c.last hc hpre hpost hslots htSlots
  refine ⟨blocks, hcopy.first_length, hcopy.middle_length, hcopy.last_length, hcopy.gapped, ?_⟩
  change (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep u (gateOpenRail p g))).image Direction.east.position = _ at hrail
  rw [BoxMask.lineBoxes_keep] at hrail
  · exact hrail
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

end PushPuzzle.PushS.PortLayout

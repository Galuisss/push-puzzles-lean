/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxisTrains

/-! Every successful gate middle-axis prefix keeps both prescribed rigid trains unmerged. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The upper rod and middle train keep their prescribed lengths and an intervening gap. -/
structure GateAxisTrainShape (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (blocks : TwoBlocks) : Prop where
  first_length : blocks.firstLength = readDepth p upper.level - 1
  last_length : blocks.lastLength = p.H - readDepth p 1 - readDepth p upper.level - 4
  gapped : blocks.Gapped
  slots : (u.boxes ∩ gateAxis p (g.left + 1)).image Direction.south.position = blocks.slots

/-- Every successful actual middle-axis prefix consists of the original two rigid, unmerged trains. -/
theorem physicalInstance_gateAxis_train_shape (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsuSide : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ blocks, GateAxisTrainShape p g upper u blocks := by
  let b := gateAxisTrainBlocks p upper initial
  let c := gateAxisTrainBlocks p upper target
  have hb := l.gateAxisTrainBlocks_gapped p hl hM hu initial
  have hc := l.gateAxisTrainBlocks_gapped p hl hM hu target
  have hpos := l.gateAxisTrainBlocks_positive p hl hM hu initial
  have hslt := l.physicalInstance_gateAxis_train_initial_slots p hl hM ha initial target hg hk hu hsuSide hp
  have htlt := l.physicalInstance_gateAxis_train_target_slots p hl hM ha initial target hg hk hu hsuSide hp ht
  have hpre := l.physicalInstance_gateAxis_admissible_prefix p hl hM ha initial target hg hk hsu hut ht
  have hpost := l.physicalInstance_gateAxis_admissible_suffix p hl hM ha initial target hg hk hsu hut ht
  obtain ⟨blocks, hcopy, hrail⟩ := b.admissible_at hpos hb c.first c.last hc hpre hpost hslt htlt
  refine ⟨blocks, hcopy.first_length, hcopy.last_length, hcopy.gapped, ?_⟩
  change (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep u (gateAxis p (g.left + 1)))).image Direction.south.position = _ at hrail
  rw [BoxMask.lineBoxes_keep] at hrail
  · exact hrail
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

end PushPuzzle.PushS.PortLayout

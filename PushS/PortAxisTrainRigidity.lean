/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisTrains
public import PushS.TrainDynamics

/-! The two outer rods and middle train remain rigid on every successful ordinary shared axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The actual three ordinary-axis trains keep both outer rod lengths and the middle length. -/
structure OrdinaryAxisTrainShape (p : Scales.Parameters) (upper lower : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (blocks : ThreeBlocks) : Prop where
  first_length : blocks.firstLength = readDepth p upper.level - 1
  middle_length : blocks.middleLength = p.H - readDepth p upper.level - readDepth p lower.level - 4
  last_length : blocks.lastLength = readDepth p lower.level - 1
  gapped : blocks.Gapped
  slots : (u.boxes ∩ ordinaryAxis p upper.port).image Direction.south.position = blocks.slots

/-- Each successful actual ordinary-axis prefix consists of the original three rigid, unmerged trains. -/
theorem physicalInstance_ordinaryAxis_train_shape (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ blocks, OrdinaryAxisTrainShape p upper lower u blocks := by
  let b := ordinaryAxisTrainBlocks p upper lower initial
  let c := ordinaryAxisTrainBlocks p upper lower target
  have hb := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow initial
  have hc := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow target
  have hpos := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow initial
  have hslots := l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM ha initial target hu hlow hsuSide hslSide hport
  have htSlots := l.physicalInstance_ordinaryAxis_train_target_slots p hl hM ha initial target hu hlow hsuSide hslSide hport ht
  have hpre := l.physicalInstance_ordinaryAxis_admissible_prefix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht
  have hpost := l.physicalInstance_ordinaryAxis_admissible_suffix p hl hM ha initial target hu hlow hsuSide hslSide hport hsu hut ht
  obtain ⟨blocks, hcopy, hrail⟩ := b.admissible_at hpos hb c.first c.middle c.last hc hpre hpost hslots htSlots
  refine ⟨blocks, hcopy.first_length, hcopy.middle_length, hcopy.last_length, hcopy.gapped, ?_⟩
  change (lineBoxes .south (p.x upper.port) (BoxMask.keep u (ordinaryAxis p upper.port))).image Direction.south.position = _ at hrail
  rw [BoxMask.lineBoxes_keep] at hrail
  · exact hrail
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

end PushPuzzle.PushS.PortLayout

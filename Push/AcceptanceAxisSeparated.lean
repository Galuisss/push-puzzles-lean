/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceAxisInventory
public import Push.AcceptanceTrainBlocks
public import PushS.PortAxisTrainRigidity

/-! A terminal five-hole certificate supplies actual separated ordinary-axis blocks before any final gap calculation. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceTrainBlocks

/-- The actual ordinary-axis rods and middle train retain their prescribed lengths, with contact allowed. -/
structure OrdinaryAxisBlocks (p : Scales.Parameters) (upper lower : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (blocks : ThreeBlocks) : Prop where
  first_length : blocks.firstLength = readDepth p upper.level - 1
  middle_length : blocks.middleLength = p.H - readDepth p upper.level - readDepth p lower.level - 4
  last_length : blocks.lastLength = readDepth p lower.level - 1
  separated : blocks.Separated
  slots : (u.boxes ∩ ordinaryAxis p upper.port).image Direction.south.position = blocks.slots

/-- Once the two actual gaps are positive, the separated blocks give the existing ordinary-axis train shape. -/
theorem OrdinaryAxisBlocks.toTrainShape {p : Scales.Parameters} {upper lower : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {blocks : ThreeBlocks}
    (shape : OrdinaryAxisBlocks p upper lower u blocks) (gapped : blocks.Gapped) :
    OrdinaryAxisTrainShape p upper lower u blocks :=
  ⟨shape.first_length, shape.middle_length, shape.last_length, gapped, shape.slots⟩

/-- A real accepted axis with five terminal holes retains its original three separated trains at every source prefix. -/
theorem canonical_ordinaryAxis_blocks_of_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsuSide : upper.side = .upper) (hslSide : lower.side = .lower) (hport : lower.port = upper.port)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ ordinaryAxis p upper.port).card = 5) :
    ∃ blocks, OrdinaryAxisBlocks p upper lower u blocks := by
  let b := ordinaryAxisTrainBlocks p upper lower (l.canonical initial)
  have positive := l.ordinaryAxisTrainBlocks_positive p hl hM hu hlow (l.canonical initial)
  have gapped := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow (l.canonical initial)
  have before := canonical_ordinaryAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hu hlow hsuSide hslSide hport hsu hut accepted inventory
  have source := l.physicalInstance_ordinaryAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hu hlow hsuSide hslSide hport
  obtain ⟨blocks, copy, slots⟩ := three_admissible_separated b positive ⟨gapped.1.le, gapped.2.le⟩ source before
  refine ⟨blocks, copy.first_length, copy.middle_length, copy.last_length, copy.separated, ?_⟩
  have mask : (lineBoxes .south (p.x upper.port) (BoxMask.keep u (ordinaryAxis p upper.port)) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ ordinaryAxis p upper.port :=
    BoxMask.lineBoxes_keep (R := ordinaryAxis p upper.port) (axis := .south) (lane := p.x upper.port)
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.south.position) mask).symm.trans slots

end PushPuzzle.Push.AcceptanceSoundness

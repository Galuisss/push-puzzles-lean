/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateAxisInventory
public import Push.AcceptanceTrainBlocks
public import PushS.PortGateAxisTrainRigidity

/-! A four-hole terminal gate-axis certificate supplies its two actual separated trains. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram AcceptanceTrainBlocks

/-- The actual gate-axis upper rod and middle train keep their prescribed lengths, with contact allowed. -/
structure GateAxisBlocks (p : Scales.Parameters) (g : Placement) (upper : Endpoint)
    (u : State (p.W + 1) (p.H + 1)) (blocks : TwoBlocks) : Prop where
  first_length : blocks.firstLength = readDepth p upper.level - 1
  last_length : blocks.lastLength = p.H - readDepth p 1 - readDepth p upper.level - 4
  separated : blocks.Separated
  slots : (u.boxes ∩ gateAxis p (g.left + 1)).image Direction.south.position = blocks.slots

/-- A positive actual internal gap promotes the separated gate-axis blocks to the existing train shape. -/
theorem GateAxisBlocks.toTrainShape {p : Scales.Parameters} {g : Placement} {upper : Endpoint}
    {u : State (p.W + 1) (p.H + 1)} {blocks : TwoBlocks}
    (shape : GateAxisBlocks p g upper u blocks) (gapped : blocks.Gapped) :
    GateAxisTrainShape p g upper u blocks :=
  ⟨shape.first_length, shape.last_length, gapped, shape.slots⟩

/-- A real accepted gate axis with four terminal holes retains its original two separated trains at every source prefix. -/
theorem canonical_gateAxis_blocks_of_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (inventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4) :
    ∃ blocks, GateAxisBlocks p g upper u blocks := by
  let b := gateAxisTrainBlocks p upper (l.canonical initial)
  have positive := l.gateAxisTrainBlocks_positive p hl hM hu (l.canonical initial)
  have gapped := l.gateAxisTrainBlocks_gapped p hl hM hu (l.canonical initial)
  have before := canonical_gateAxis_admissible_prefix_of_terminal l p hl hM haxes initial target hgate
    hg hk hsu hut accepted inventory
  have source := l.physicalInstance_gateAxis_train_initial_slots p hl hM haxes (l.canonical initial) (l.canonical target)
    hg hk hu hs hp
  obtain ⟨blocks, copy, slots⟩ := two_admissible_separated b positive gapped.le source before
  refine ⟨blocks, copy.first_length, copy.last_length, copy.separated, ?_⟩
  have mask : (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep u (gateAxis p (g.left + 1))) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ gateAxis p (g.left + 1) :=
    BoxMask.lineBoxes_keep (R := gateAxis p (g.left + 1)) (axis := .south) (lane := p.x (g.left + 1))
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.south.position) mask).symm.trans slots

end PushPuzzle.Push.AcceptanceSoundness

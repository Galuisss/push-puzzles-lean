/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateRailInventory
public import Push.AcceptanceTrainBlocks
public import PushS.PortGateTrainRigidity
import all PushS.PortSegments

/-! Balanced accepted gate rails carry their three original ordered fixed-length blocks. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

/-- The complete actual gate rail with its three original train lengths, allowing adjacent blocks. -/
structure GateRailBlocks (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (u : State (p.W + 1) (p.H + 1)) (blocks : ThreeBlocks) : Prop where
  first_length : blocks.firstLength = p.D - kind.kappa.toNat
  middle_length : blocks.middleLength = 2
  last_length : blocks.lastLength = p.D - 14
  separated : blocks.Separated
  slots : (u.boxes ∩ gateOpenRail p g).image Direction.east.position = blocks.slots

/-- Nonempty internal gaps turn the same weak blocks into the genuine rail shape. -/
theorem GateRailBlocks.toTrainShape {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u : State (p.W + 1) (p.H + 1)} {blocks : ThreeBlocks}
    (shape : GateRailBlocks p g kind u blocks) (gapped : blocks.Gapped) : GateTrainShape p g kind u blocks :=
  ⟨shape.first_length, shape.middle_length, shape.last_length, gapped, shape.slots⟩

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ []) {g : Placement} (hg : g ∈ placements l)
  {kind : Shuttle.Kind} (hk : g.gate = some kind)

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate hg hk

/-- Every balanced actual gate-rail prefix follows its original horizontal line semantics. -/
theorem canonical_gateRail_admissible_prefix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    Relation.ReflTransGen (LineAdmissible (I).board none .east (p.H - readDepth p 1))
      (BoxMask.keep (I).initial (gateOpenRail p g)) (BoxMask.keep u (gateOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (gateOpenRail_runClosed p g) ?_
    (canonical_gateRail_balanced_prefix_of_terminal l p hl hM haxes initial target hgate hg hk
      hsu hut accepted axisInventory railInventory)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- The suffix of the same accepted gate-rail path follows the same masked line semantics. -/
theorem canonical_gateRail_admissible_suffix_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    Relation.ReflTransGen (LineAdmissible (I).board none .east (p.H - readDepth p 1))
      (BoxMask.keep u (gateOpenRail p g)) (BoxMask.keep t (gateOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (gateOpenRail_runClosed p g) ?_ ?_
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1
  · apply Path.enrich hut
    intro a b hua step hbt
    exact ⟨step, canonical_gateRail_inventory_step_of_terminal l p hl hM haxes initial target hgate hg hk
      (hsu.trans hua) step hbt accepted axisInventory railInventory⟩

/-- Every balanced actual accepted rail retains its original three separated marked blocks. -/
theorem canonical_gateRail_blocks_of_terminal {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    (axisInventory : (holes t ∩ gateAxis p (g.left + 1)).card = 4)
    (railInventory : (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11) :
    ∃ blocks, GateRailBlocks p g kind u blocks := by
  let source := gateTrainBlocks p g kind (l.canonical initial)
  have positive := gateTrainBlocks_positive p g kind (l.canonical initial)
  have gapped := gateTrainBlocks_gapped p g kind (l.canonical initial)
  have slots := l.physicalInstance_gate_train_initial_slots p hl hM haxes
    (l.canonical initial) (l.canonical target) hg hk
  have hpre := canonical_gateRail_admissible_prefix_of_terminal l p hl hM haxes initial target hgate hg hk
    hsu hut accepted axisInventory railInventory
  obtain ⟨blocks, copy, actual⟩ := AcceptanceTrainBlocks.three_admissible_separated source positive
    ⟨le_of_lt gapped.1, le_of_lt gapped.2⟩ slots hpre
  refine ⟨blocks, copy.first_length, copy.middle_length, copy.last_length, copy.separated, ?_⟩
  have mask : (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep u (gateOpenRail p g)) :
      Finset (Cell (p.W + 1) (p.H + 1))) = u.boxes ∩ gateOpenRail p g :=
    BoxMask.lineBoxes_keep (R := gateOpenRail p g) (axis := .east) (lane := p.H - readDepth p 1)
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.east.position) mask).symm.trans actual

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

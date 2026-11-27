/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWireBalanced
public import Push.AcceptanceRailReadoutTrain
import all PushS.PortWireTrains
import all PushS.PortSegments

/-! The actual accepted WIRE inventory preserves its complete single train and physical motion. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout PushS.RowLabels AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  (hgate : l.gateCenterCoordinates ≠ [])

local notation "I" => l.canonicalInstance p hl hM haxes initial target

include hgate

/-- Every actual accepted WIRE prefix follows its original masked horizontal line. -/
private theorem canonical_wire_admissible_prefix {g : Placement} (hg : g ∈ placements l)
    (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Relation.ReflTransGen (LineAdmissible (I).board none .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level))
      (BoxMask.keep (I).initial (wireOpenRail p g)) (BoxMask.keep u (wireOpenRail p g)) := by
  apply BoxMask.keep_admissible_reachable (wireOpenRail_runClosed p g) ?_
    (canonical_wire_balanced_prefix l p hl hM haxes initial target hgate hg hw hsu hut accepted)
  intro q hq
  exact (Finset.mem_filter.mp hq).2.1

/-- Every actual accepted WIRE retains its full original consecutive box train. -/
theorem canonical_wire_train_shape {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    ∃ first, WireTrainShape p g u first := by
  have source := l.encodedSegments_wire_train_slots p hl hM haxes (l.canonical initial) hg hw
    (I).initial (l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target))
  have hpre := canonical_wire_admissible_prefix l p hl hM haxes initial target hgate hg hw hsu hut accepted
  obtain ⟨first, slots⟩ := interval_admissible (l.wireTrainLength_positive p hl hg hw)
    (wireTrainStart p g (l.canonical initial)) hpre source
  refine ⟨first, ⟨?_⟩⟩
  have mask : (lineBoxes .east
      (if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (BoxMask.keep u (wireOpenRail p g)) : Finset (Cell (p.W + 1) (p.H + 1))) =
      u.boxes ∩ wireOpenRail p g :=
    BoxMask.lineBoxes_keep (R := wireOpenRail p g) (axis := .east)
      (lane := if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
      (fun _ hq => (Finset.mem_filter.mp hq).2.1) u
  exact (congrArg (Finset.image Direction.east.position) mask).symm.trans slots

/-- Each actual successful WIRE step carries the same complete train marks and forcing coordinates. -/
theorem canonical_wire_train_step {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (step : Step (I).board none u v)
    (hvt : Reachable (I).board none v t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t)) :
    Nonempty (WireTrainStep p g (I).board u v) := by
  obtain ⟨first, before⟩ := canonical_wire_train_shape l p hl hM haxes initial target hgate hg hw
    hsu ((Relation.ReflTransGen.single step).trans hvt) accepted
  obtain ⟨next, after⟩ := canonical_wire_train_shape l p hl hM haxes initial target hgate hg hw
    (hsu.tail step) hvt accepted
  apply AcceptanceRailReadout.wire_train_step_of_shapes p g (l.wireTrainLength_positive p hl hg hw) before after
  exact BoxMask.keep_admissible (axis := .east)
    (lane := if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (wireOpenRail_runClosed p g) (fun _ hq => (Finset.mem_filter.mp hq).2.1) step
    (canonical_wire_inventory_step l p hl hM haxes initial target hgate hg hw hsu step hvt accepted)

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTrainReadout
public import PushS.PortCanonicalSignals
public import PushS.TrainUnique
import all PushS.PortGateIndexing
import all PushS.PortGateTrains
import all PushS.PortLayoutCoordinates

/-! Actual complete gate occupancy uniquely determines its three train starts. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- Two complete physical train descriptions of the same actual gate rail coincide. -/
theorem GateTrainShape.unique {p : Scales.Parameters} {g : Placement} {kind : Shuttle.Kind}
    {u : State (p.W + 1) (p.H + 1)} {b c : ThreeBlocks}
    (hb : GateTrainShape p g kind u b) (hc : GateTrainShape p g kind u c) : b = c :=
  ThreeBlocks.eq_of_slots hb.positive ⟨le_of_lt hb.gapped.1, le_of_lt hb.gapped.2⟩
    ⟨le_of_lt hc.gapped.1, le_of_lt hc.gapped.2⟩
    (hb.first_length.trans hc.first_length.symm) (hb.middle_length.trans hc.middle_length.symm)
    (hb.last_length.trans hc.last_length.symm) (hb.slots.symm.trans hc.slots)

/-- The solved actual gate has exactly the literal target train starts. -/
theorem physicalInstance_gate_train_target_shape (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {t : State (p.W + 1) (p.H + 1)} (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    GateTrainShape p g kind t (gateTrainBlocks p g kind target) := by
  refine ⟨rfl, rfl, rfl, gateTrainBlocks_gapped p g kind target, ?_⟩
  have hs := l.physicalInstance_gate_train_target_slots p hl hM ha initial target hg hk ht
  change (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep t (gateOpenRail p g))).image Direction.east.position = _ at hs
  rw [BoxMask.lineBoxes_keep] at hs
  · exact hs
  · intro q hq
    exact (Finset.mem_filter.mp hq).2.1

/-- Every canonical actual gate identifies the short bit and relay bit, excluding a relay fault. -/
theorem canonical_gate_no_relay_fault (l : PortLayout) (p : Scales.Parameters) (axes : List Bool)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    ¬ (6 ≤ (gateTrainPlacement p g (gateTrainBlocks p g kind (l.canonical axes))).short ∧
      2 ≤ (gateTrainPlacement p g (gateTrainBlocks p g kind (l.canonical axes))).right) := by
  have hread := l.canonical_gate_read axes hg hk
  have hbit := hread.2.1.trans hread.2.2.symm
  have hright : p.x g.right = p.x (g.left + 1) + p.D := by
    simpa only [(placement_gate_shape l hg hk).2, Nat.add_assoc] using x_succ_eq p (g.left + 1)
  have hD := readDepth_readLength_margin p 0 0
  dsimp only [gateTrainPlacement, gateTrainBlocks]
  rw [hbit]
  cases (l.canonical axes).internal.getD (g.internal + 2) false <;>
    simp only [Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, ite_true, ite_false] <;> omega

end PushPuzzle.PushS.PortLayout

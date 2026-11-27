/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortRailProjection
public import PushS.PortGateUpdates
public import PushS.TrainRigidity
import all PushS.PortGateIndexing
import all PushS.PortGateRail
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates
import all PushS.OrderedSlots

/-! The complete actual gate rail consists of three ordered fixed-length box trains. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The three literal canonical box trains on an actual three-port horizontal rail. -/
@[expose] def gateTrainBlocks (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : SignalState) : ThreeBlocks where
  first := (p.x g.left : ℤ) + 2 + (state.internal.getD g.internal false).toNat
  middle := (p.x (g.left + 1) : ℤ) + (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) + 1
  last := (p.x (g.left + 1) : ℤ) + 12 + (state.internal.getD (g.internal + 2) false).toNat
  firstLength := p.D - kind.kappa.toNat
  middleLength := 2
  lastLength := p.D - 14

private theorem x_succ_eq (p : Scales.Parameters) (i : ℕ) : p.x (i + 1) = p.x i + p.D := by
  simp only [Scales.Parameters.x, Nat.add_mul, Nat.one_mul]

/-- All three canonical gate trains have positive lengths. -/
theorem gateTrainBlocks_positive (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (state : SignalState) :
    (gateTrainBlocks p g kind state).Positive := by
  have hD := readDepth_readLength_margin p 0 0
  have hk : kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  change 0 < p.D - kind.kappa.toNat ∧ 0 < 2 ∧ 0 < p.D - 14
  omega

/-- Both canonical internal gaps of an actual gate train layout are nonempty. -/
theorem gateTrainBlocks_gapped (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (state : SignalState) :
    (gateTrainBlocks p g kind state).Gapped := by
  have hD := readDepth_readLength_margin p 0 0
  have hmid := x_succ_eq p g.left
  have hk : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
  have hL := Bool.toNat_le (state.internal.getD g.internal false)
  have hR := Bool.toNat_le (state.internal.getD (g.internal + 2) false)
  have hshort : 1 ≤ (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ∧
      (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ≤ 6 := by split <;> decide +kernel
  change (p.x g.left : ℤ) + 2 + (state.internal.getD g.internal false).toNat + (p.D - kind.kappa.toNat : ℕ) <
      (p.x (g.left + 1) : ℤ) + (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) + 1 ∧
    (p.x (g.left + 1) : ℤ) + (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) + 1 + (2 : ℕ) <
      (p.x (g.left + 1) : ℤ) + 12 + (state.internal.getD (g.internal + 2) false).toNat
  omega

private theorem gate_train_slot_bounds (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : SignalState) (hshape : g.right = g.left + 2) {x : ℤ}
    (hx : x ∈ (gateTrainBlocks p g kind state).slots) : (p.x g.left : ℤ) < x ∧ x < p.x g.right := by
  have hg := gateTrainBlocks_gapped p g kind state
  have hb : (gateTrainBlocks p g kind state).Separated := ⟨le_of_lt hg.1, le_of_lt hg.2⟩
  have hs := (gateTrainBlocks p g kind state).slots_bounds hb hx
  have hD := readDepth_readLength_margin p 0 0
  have hmid := x_succ_eq p (g.left + 1)
  have hright : p.x g.right = p.x (g.left + 1) + p.D := by simpa only [hshape, Nat.add_assoc] using hmid
  have hR := Bool.toNat_le (state.internal.getD (g.internal + 2) false)
  change (p.x g.left : ℤ) + 2 + (state.internal.getD g.internal false).toNat ≤ x ∧
    x < (p.x (g.left + 1) : ℤ) + 12 + (state.internal.getD (g.internal + 2) false).toNat + (p.D - 14 : ℕ) at hs
  constructor <;> omega

private theorem gate_train_slots_inside (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind)
    (state : SignalState) (hshape : g.right = g.left + 2) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = p.H - readDepth p 1) (hx : (q.1.val : ℤ) ∈ (gateTrainBlocks p g kind state).slots) :
    q ∈ gateOpenRail p g := by
  have hb := gate_train_slot_bounds p g kind state hshape hx
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy, by omega, by omega⟩

/-- Canonical physical gate-rail occupancy is exactly the union of its three train intervals. -/
theorem encodedSegments_gate_train_boxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (BoxMask.keep s (gateOpenRail p g)).boxes ↔
      q.2.val = p.H - readDepth p 1 ∧ (q.1.val : ℤ) ∈ (gateTrainBlocks p g kind state).slots := by
  change q ∈ s.boxes ∩ gateOpenRail p g ↔ _
  by_cases hr : q ∈ gateOpenRail p g
  · have hbox : q ∈ s.boxes ↔ q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
      rw [← hholes]
      simp only [mem_holes, not_not]
    rw [Finset.mem_inter, hbox]
    simp only [hr, and_true]
    rw [l.encodedSegments_gateOpenRail_mem p hl hM ha state hg hk hr]
    have hrow := (Finset.mem_filter.mp hr).2
    rw [ThreeBlocks.mem_slots]
    have hD := readDepth_readLength_margin p 0 0
    have hmid := x_succ_eq p g.left
    have hright : p.x g.right = p.x (g.left + 1) + p.D := by
      simpa only [(placement_gate_shape l hg hk).2, Nat.add_assoc] using x_succ_eq p (g.left + 1)
    have hkappa : 2 ≤ kind.kappa.toNat ∧ kind.kappa.toNat ≤ 4 := by cases kind <;> decide +kernel
    have hL := Bool.toNat_le (state.internal.getD g.internal false)
    have hR := Bool.toNat_le (state.internal.getD (g.internal + 2) false)
    have hRN := Bool.toNat_le (!(state.internal.getD (g.internal + 2) false))
    have hnot : (state.internal.getD (g.internal + 2) false).toNat + (!(state.internal.getD (g.internal + 2) false)).toNat = 1 := by
      cases state.internal.getD (g.internal + 2) false <;> decide +kernel
    have hshort : 1 ≤ (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ∧
        (if state.internal.getD (g.internal + 1) false then 6 else 1 : ℕ) ≤ 6 := by split <;> decide +kernel
    simp only [gateTrainBlocks]
    omega
  · constructor
    · intro hq
      exact False.elim (hr (Finset.mem_inter.mp hq).2)
    · intro hq
      exact False.elim (hr (gate_train_slots_inside p g kind state (placement_gate_shape l hg hk).2 hq.1 hq.2))

/-- Every canonical actual retained gate rail has exactly the three prescribed ordered coordinate intervals. -/
theorem encodedSegments_gate_train_slots (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    (RowLabels.lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep s (gateOpenRail p g))).image Direction.east.position =
      (gateTrainBlocks p g kind state).slots := by
  ext x
  constructor
  · intro hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hx
    have hs := l.encodedSegments_gate_train_boxes p hl hM ha state hg hk s hholes q
    exact (hs.mp (Finset.mem_filter.mp hq).1).2
  · intro hx
    have hb := gate_train_slot_bounds p g kind state (placement_gate_shape l hg hk).2 hx
    have hx0 : 0 ≤ x := by omega
    have hxval : (x.toNat : ℤ) = x := Int.toNat_of_nonneg hx0
    have hxW := x_add_readLength_lt_W p ((gate_port_bounds l hl hg hk).2.trans_le ha) 0
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨x.toNat, by omega⟩, ⟨p.H - readDepth p 1, by have hH := readDepth_add_lt_H p 1; omega⟩)
    have hq : q ∈ (BoxMask.keep s (gateOpenRail p g)).boxes :=
      (l.encodedSegments_gate_train_boxes p hl hM ha state hg hk s hholes q).mpr ⟨rfl, by simpa only [q, hxval] using hx⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hxval⟩

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The physical initial gate train slots are the literal canonical intervals. -/
theorem physicalInstance_gate_train_initial_slots {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep (I).initial (gateOpenRail p g))).image Direction.east.position =
      (gateTrainBlocks p g kind initial).slots := by
  exact l.encodedSegments_gate_train_slots p hl hM ha initial hg hk (I).initial
    (l.physicalInstance_initial_holes p hl hM ha initial target)

/-- The solved physical gate train slots are the literal canonical target intervals. -/
theorem physicalInstance_gate_train_target_slots {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (I).board.goals) :
    (lineBoxes .east (p.H - readDepth p 1) (BoxMask.keep t (gateOpenRail p g))).image Direction.east.position =
      (gateTrainBlocks p g kind target).slots := by
  apply l.encodedSegments_gate_train_slots p hl hM ha target hg hk t
  change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
  rw [ht]
  exact l.physicalInstance_goal_holes p hl hM ha initial target

end Solution
end PushPuzzle.PushS.PortLayout

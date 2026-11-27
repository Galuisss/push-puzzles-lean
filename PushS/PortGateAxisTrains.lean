/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortRailProjection
public import PushS.PortGateAxisUpdates
public import PushS.TwoTrainDynamics
import all PushS.PortLayoutCoordinates

/-! The literal two canonical trains on a three-port gate's middle axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS RowLabels

/-- The upper outer rod and middle train above a gate's working row. -/
@[expose] def gateAxisTrainBlocks (p : Scales.Parameters) (upper : Endpoint) (state : SignalState) : TwoBlocks where
  first := 1
  last := (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat
  firstLength := readDepth p upper.level - 1
  lastLength := p.H - readDepth p 1 - readDepth p upper.level - 4

private theorem gate_axis_train_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper : Endpoint} (hu : upper ∈ l.endpoints) :
    16384 ≤ readDepth p upper.level ∧ readDepth p upper.level + readDepth p 1 + 128 < p.H := by
  have hy := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have hDu := readDepth_add_lt_D p upper.level
  have hD1 := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  exact ⟨hy, by omega⟩

/-- Both canonical gate-axis trains have positive prescribed lengths. -/
theorem gateAxisTrainBlocks_positive (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper : Endpoint} (hu : upper ∈ l.endpoints) (state : SignalState) :
    (gateAxisTrainBlocks p upper state).Positive := by
  obtain ⟨hy, hsum⟩ := gate_axis_train_bounds l p hl hM hu
  change 0 < readDepth p upper.level - 1 ∧ 0 < p.H - readDepth p 1 - readDepth p upper.level - 4
  omega

/-- The upper ordinary near pocket separates both canonical gate-axis trains. -/
theorem gateAxisTrainBlocks_gapped (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper : Endpoint} (hu : upper ∈ l.endpoints) (state : SignalState) :
    (gateAxisTrainBlocks p upper state).Gapped := by
  have hy := (gate_axis_train_bounds l p hl hM hu).1
  change (1 : ℤ) + (readDepth p upper.level - 1 : ℕ) <
    (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat
  omega

private theorem gate_axis_slot_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper : Endpoint} (hu : upper ∈ l.endpoints) (state : SignalState)
    {y : ℤ} (hy : y ∈ (gateAxisTrainBlocks p upper state).slots) : 0 < y ∧ y < p.H - readDepth p 1 := by
  have hg := l.gateAxisTrainBlocks_gapped p hl hM hu state
  have hb := (gateAxisTrainBlocks p upper state).slots_bounds (le_of_lt hg) hy
  have hsum := (gate_axis_train_bounds l p hl hM hu).2
  have hbit := Bool.toNat_le (state.axes.getD upper.port false)
  change 1 ≤ y ∧ y < (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat +
    (p.H - readDepth p 1 - readDepth p upper.level - 4 : ℕ) at hb
  omega

/-- Complete canonical gate-axis occupancy is exactly its two fixed-length train intervals. -/
theorem encodedSegments_gateAxis_train_boxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (BoxMask.keep s (gateAxis p (g.left + 1))).boxes ↔
      q.1.val = p.x (g.left + 1) ∧ (q.2.val : ℤ) ∈ (gateAxisTrainBlocks p upper state).slots := by
  change q ∈ s.boxes ∩ gateAxis p (g.left + 1) ↔ _
  by_cases hr : q ∈ gateAxis p (g.left + 1)
  · have hbox : q ∈ s.boxes ↔ q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
      rw [← hholes]
      simp only [mem_holes, not_not]
    rw [Finset.mem_inter, hbox]
    simp only [hr, and_true]
    rw [l.encodedSegments_gateAxis_mem p hl hM ha state hg hk hu hsu hp hr, TwoBlocks.mem_slots]
    have hrow := (Finset.mem_filter.mp hr).2
    obtain ⟨hy, hsum⟩ := gate_axis_train_bounds l p hl hM hu
    have hbit := Bool.toNat_le (state.axes.getD (g.left + 1) false)
    simp only [gateAxisTrainBlocks, hp]
    omega
  · constructor
    · intro hq
      exact False.elim (hr (Finset.mem_inter.mp hq).2)
    · intro hq
      have hy := gate_axis_slot_bounds l p hl hM hu state hq.2
      exact False.elim (hr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq.1, by omega, by omega⟩))

/-- The canonical gate-axis coordinate slots are the two literal prescribed intervals. -/
theorem encodedSegments_gateAxis_train_slots (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep s (gateAxis p (g.left + 1)))).image Direction.south.position =
      (gateAxisTrainBlocks p upper state).slots := by
  ext y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact ((l.encodedSegments_gateAxis_train_boxes p hl hM ha state hg hk hu hsu hp s hholes q).mp
      (Finset.mem_filter.mp hq).1).2
  · intro hy
    have hb := gate_axis_slot_bounds l p hl hM hu state hy
    have hyval : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hu).trans_le ha) 0
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x (g.left + 1), by rw [← hp]; omega⟩, ⟨y.toNat, by omega⟩)
    have hq := (l.encodedSegments_gateAxis_train_boxes p hl hM ha state hg hk hu hsu hp s hholes q).mpr
      ⟨rfl, by simpa only [q, hyval] using hy⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hyval⟩

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The initial physical gate-axis slots are the literal canonical pair of trains. -/
theorem physicalInstance_gateAxis_train_initial_slots {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep (I).initial (gateAxis p (g.left + 1)))).image Direction.south.position =
      (gateAxisTrainBlocks p upper initial).slots := by
  exact l.encodedSegments_gateAxis_train_slots p hl hM ha initial hg hk hu hsu hp (I).initial
    (l.physicalInstance_initial_holes p hl hM ha initial target)

/-- The solved physical gate-axis slots are the literal canonical target pair of trains. -/
theorem physicalInstance_gateAxis_train_target_slots {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)} (ht : t.boxes = (I).board.goals) :
    (lineBoxes .south (p.x (g.left + 1)) (BoxMask.keep t (gateAxis p (g.left + 1)))).image Direction.south.position =
      (gateAxisTrainBlocks p upper target).slots := by
  apply l.encodedSegments_gateAxis_train_slots p hl hM ha target hg hk hu hsu hp t
  change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
  rw [ht]
  exact l.physicalInstance_goal_holes p hl hM ha initial target

end Solution
end PushPuzzle.PushS.PortLayout

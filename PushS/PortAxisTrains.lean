/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortRailProjection
public import PushS.TrainRigidity
import all PushS.PortOrdinaryAxis
import all PushS.PortAxisMacro
import all PushS.PortEndpointCounts
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates

/-! The three literal canonical box trains of an actual ordinary shared main axis. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe RowLabels

/-- The two outer rods and middle train of an ordinary complete shared axis. -/
@[expose] def ordinaryAxisTrainBlocks (p : Scales.Parameters) (upper lower : Endpoint)
    (state : SignalState) : ThreeBlocks where
  first := 1
  middle := (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat
  last := (p.H : ℤ) - readDepth p lower.level + 1
  firstLength := readDepth p upper.level - 1
  middleLength := p.H - readDepth p upper.level - readDepth p lower.level - 4
  lastLength := readDepth p lower.level - 1

private theorem axis_train_bounds (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints) :
    16384 ≤ readDepth p upper.level ∧ 16384 ≤ readDepth p lower.level ∧
      readDepth p upper.level + readDepth p lower.level + 128 < p.H := by
  have hyu := readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  have hyl := readDepth_ge p (l.endpoints_level_bounds p hl hM hlow).1 (l.endpoints_level_bounds p hl hM hlow).2
  have hDu := readDepth_add_lt_D p upper.level
  have hDl := readDepth_add_lt_D p lower.level
  have hH : p.H = 2 * p.D := rfl
  exact ⟨hyu, hyl, by omega⟩

/-- Every actual ordinary axis has three nonempty canonical box trains. -/
theorem ordinaryAxisTrainBlocks_positive (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (state : SignalState) : (ordinaryAxisTrainBlocks p upper lower state).Positive := by
  obtain ⟨hyu, hyl, hsum⟩ := axis_train_bounds l p hl hM hu hlow
  change 0 < readDepth p upper.level - 1 ∧
    0 < p.H - readDepth p upper.level - readDepth p lower.level - 4 ∧ 0 < readDepth p lower.level - 1
  omega

/-- Both actual ordinary-axis near pockets separate the canonical three trains. -/
theorem ordinaryAxisTrainBlocks_gapped (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (state : SignalState) : (ordinaryAxisTrainBlocks p upper lower state).Gapped := by
  obtain ⟨hyu, hyl, hsum⟩ := axis_train_bounds l p hl hM hu hlow
  have hb := Bool.toNat_le (state.axes.getD upper.port false)
  change (1 : ℤ) + (readDepth p upper.level - 1 : ℕ) <
      (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat ∧
    (readDepth p upper.level : ℤ) + 2 + (state.axes.getD upper.port false).toNat +
      (p.H - readDepth p upper.level - readDepth p lower.level - 4 : ℕ) <
      (p.H : ℤ) - readDepth p lower.level + 1
  omega

private theorem axis_train_slots_inside (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (state : SignalState) {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x upper.port)
    (hy : (q.2.val : ℤ) ∈ (ordinaryAxisTrainBlocks p upper lower state).slots) : q ∈ ordinaryAxis p upper.port := by
  have hg := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow state
  have hb := (ordinaryAxisTrainBlocks p upper lower state).slots_bounds ⟨le_of_lt hg.1, le_of_lt hg.2⟩ hy
  have hyl := (axis_train_bounds l p hl hM hu hlow).2.1
  change 1 ≤ (q.2.val : ℤ) ∧ (q.2.val : ℤ) < (p.H : ℤ) - readDepth p lower.level + 1 + (readDepth p lower.level - 1 : ℕ) at hb
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by omega⟩

/-- Complete canonical physical ordinary-axis occupancy is exactly the three fixed-length intervals. -/
theorem encodedSegments_ordinaryAxis_train_boxes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ (BoxMask.keep s (ordinaryAxis p upper.port)).boxes ↔
      q.1.val = p.x upper.port ∧ (q.2.val : ℤ) ∈ (ordinaryAxisTrainBlocks p upper lower state).slots := by
  change q ∈ s.boxes ∩ ordinaryAxis p upper.port ↔ _
  by_cases hr : q ∈ ordinaryAxis p upper.port
  · have hbox : q ∈ s.boxes ↔ q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
      rw [← hholes]
      simp only [mem_holes, not_not]
    have he := Finset.ext_iff.mp (l.encodedSegments_ordinaryAxis p hl hM ha state hu hlow hsu hsl hport) q
    simp only [Finset.mem_inter, hr, and_true] at he
    rw [Finset.mem_inter, hbox]
    simp only [hr, and_true]
    rw [he, finite_mem, ordinaryAxisSegments, pointHoles_append, Finset.mem_union, axis_mem, axis_mem]
    have hrow := (Finset.mem_filter.mp hr).2
    rw [ThreeBlocks.mem_slots]
    obtain ⟨hyu, hyl, hsum⟩ := axis_train_bounds l p hl hM hu hlow
    have hb := Bool.toNat_le (state.axes.getD upper.port false)
    have hnot := Bool.toNat_le (!(state.axes.getD upper.port false))
    have hbits : (state.axes.getD upper.port false).toNat + (!(state.axes.getD upper.port false)).toNat = 1 := by
      cases state.axes.getD upper.port false <;> decide +kernel
    simp only [ordinaryAxisTrainBlocks, hsu, hsl, hport, reduceCtorEq, ite_true, ite_false, onSide,
      show (coordinates p).H = p.H from rfl]
    omega
  · constructor
    · intro hq
      exact False.elim (hr (Finset.mem_inter.mp hq).2)
    · intro hq
      exact False.elim (hr (axis_train_slots_inside l p hl hM hu hlow state hq.1 hq.2))

/-- The canonical ordinary-axis coordinate slots are exactly the three prescribed train intervals. -/
theorem encodedSegments_ordinaryAxis_train_slots (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {upper lower : Endpoint} (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    (s : State (p.W + 1) (p.H + 1))
    (hholes : holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    (lineBoxes .south (p.x upper.port) (BoxMask.keep s (ordinaryAxis p upper.port))).image Direction.south.position =
      (ordinaryAxisTrainBlocks p upper lower state).slots := by
  ext y
  constructor
  · intro hy
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.mp hy
    exact ((l.encodedSegments_ordinaryAxis_train_boxes p hl hM ha state hu hlow hsu hsl hport s hholes q).mp
      (Finset.mem_filter.mp hq).1).2
  · intro hy
    have hg := l.ordinaryAxisTrainBlocks_gapped p hl hM hu hlow state
    have hb := (ordinaryAxisTrainBlocks p upper lower state).slots_bounds ⟨le_of_lt hg.1, le_of_lt hg.2⟩ hy
    have hyl := (axis_train_bounds l p hl hM hu hlow).2.1
    change 1 ≤ y ∧ y < (p.H : ℤ) - readDepth p lower.level + 1 + (readDepth p lower.level - 1 : ℕ) at hb
    have hyval : (y.toNat : ℤ) = y := Int.toNat_of_nonneg (by omega)
    have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl hu).trans_le ha) 0
    let q : Cell (p.W + 1) (p.H + 1) := (⟨p.x upper.port, by omega⟩, ⟨y.toNat, by omega⟩)
    have hq := (l.encodedSegments_ordinaryAxis_train_boxes p hl hM ha state hu hlow hsu hsl hport s hholes q).mpr
      ⟨rfl, by simpa only [q, hyval] using hy⟩
    exact Finset.mem_image.mpr ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩, hyval⟩

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- The physical initial ordinary-axis slots are its actual three canonical box trains. -/
theorem physicalInstance_ordinaryAxis_train_initial_slots {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port) :
    (lineBoxes .south (p.x upper.port) (BoxMask.keep (I).initial (ordinaryAxis p upper.port))).image Direction.south.position =
      (ordinaryAxisTrainBlocks p upper lower initial).slots := by
  exact l.encodedSegments_ordinaryAxis_train_slots p hl hM ha initial hu hlow hsu hsl hport (I).initial
    (l.physicalInstance_initial_holes p hl hM ha initial target)

/-- The solved physical ordinary-axis slots are its actual three canonical target trains. -/
theorem physicalInstance_ordinaryAxis_train_target_slots {upper lower : Endpoint}
    (hu : upper ∈ l.endpoints) (hlow : lower ∈ l.endpoints)
    (hsu : upper.side = .upper) (hsl : lower.side = .lower) (hport : lower.port = upper.port)
    {t : State (p.W + 1) (p.H + 1)} (ht : t.boxes = (I).board.goals) :
    (lineBoxes .south (p.x upper.port) (BoxMask.keep t (ordinaryAxis p upper.port))).image Direction.south.position =
      (ordinaryAxisTrainBlocks p upper lower target).slots := by
  apply l.encodedSegments_ordinaryAxis_train_slots p hl hM ha target hu hlow hsu hsl hport t
  change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
  rw [ht]
  exact l.physicalInstance_goal_holes p hl hM ha initial target

end Solution
end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainRigidity

/-! Ordered coordinate slots of two nonempty rigid trains. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

/-- Two integer-coordinate trains with their prescribed lengths. -/
structure TwoBlocks where
  first : ℤ
  last : ℤ
  firstLength : ℕ
  lastLength : ℕ

namespace TwoBlocks

/-- Use the existing ordered interval enumeration with an empty middle block. -/
@[expose] def asThree (b : TwoBlocks) : ThreeBlocks :=
  ⟨b.first, b.last, b.last, b.firstLength, 0, b.lastLength⟩

/-- Number of occupied slots in both trains. -/
@[expose] def size (b : TwoBlocks) : ℕ := b.firstLength + b.lastLength

/-- All occupied slots of the two trains. -/
@[expose] def slots (b : TwoBlocks) : Finset ℤ := b.asThree.slots

/-- The two trains occur without overlap. -/
@[expose] def Separated (b : TwoBlocks) : Prop := b.first + b.firstLength ≤ b.last

/-- The two trains have a nonempty intervening gap. -/
@[expose] def Gapped (b : TwoBlocks) : Prop := b.first + b.firstLength < b.last

/-- Both trains have at least one occupied slot. -/
@[expose] def Positive (b : TwoBlocks) : Prop := 0 < b.firstLength ∧ 0 < b.lastLength

/-- Ordered first-train then last-train coordinates. -/
@[expose] def point (b : TwoBlocks) (i : Fin b.size) : ℤ := b.asThree.point i

/-- The two intervals give exact coordinate membership. -/
theorem mem_slots (b : TwoBlocks) (x : ℤ) : x ∈ b.slots ↔
    (b.first ≤ x ∧ x < b.first + b.firstLength) ∨ (b.last ≤ x ∧ x < b.last + b.lastLength) := by
  simp only [slots, ThreeBlocks.mem_slots, asThree, Nat.cast_zero, Int.add_zero]
  omega

/-- All slots lie between the first start and the last end. -/
theorem slots_bounds (b : TwoBlocks) (hb : b.Separated) {x : ℤ} (hx : x ∈ b.slots) :
    b.first ≤ x ∧ x < b.last + b.lastLength := by
  exact b.asThree.slots_bounds ⟨hb, by change b.last + (0 : ℕ) ≤ b.last; omega⟩ hx

/-- The two-train enumeration covers exactly its occupied coordinate slots. -/
theorem slots_eq_image_point (b : TwoBlocks) : b.slots = Finset.univ.image b.point := b.asThree.slots_eq_image_point

/-- Ordered two-train slots have the prescribed total cardinality. -/
theorem card_slots (b : TwoBlocks) (hb : b.Separated) : b.slots.card = b.size :=
  b.asThree.card_slots ⟨hb, by change b.last + (0 : ℕ) ≤ b.last; omega⟩

/-- A strictly ordered actual line state has the two literal train coordinate blocks. -/
theorem ordered_coordinates {w h : ℕ} {axis : Direction} {lane : ℕ}
    (b : TwoBlocks) (hb : b.Separated) (S : OrderedLineState b.size w h axis lane)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) (i : Fin b.size) :
    axis.position (S.position i) = b.point i :=
  b.asThree.ordered_coordinates ⟨hb, by change b.last + (0 : ℕ) ≤ b.last; omega⟩ S hslots i

/-- First-train coordinates in the canonical enumeration. -/
theorem point_first (b : TwoBlocks) {j : ℕ} (hj : j < b.firstLength) :
    b.point ⟨j, by dsimp only [size]; omega⟩ = b.first + j := b.asThree.point_first hj

/-- Last-train coordinates in the canonical enumeration. -/
theorem point_last (b : TwoBlocks) {j : ℕ} (hj : j < b.lastLength) :
    b.point ⟨b.firstLength + j, by dsimp only [size]; omega⟩ = b.last + j := by
  simp only [point, asThree, ThreeBlocks.point]
  split_ifs <;> omega

/-- Every enumerated slot is occupied. -/
theorem point_mem (b : TwoBlocks) (i : Fin b.size) : b.point i ∈ b.slots := b.asThree.point_mem i

/-- Every occupied coordinate has an enumeration label. -/
theorem exists_point (b : TwoBlocks) {x : ℤ} (hx : x ∈ b.slots) : ∃ i, b.point i = x := b.asThree.exists_point hx

end TwoBlocks
end PushPuzzle.PushS.RowLabels

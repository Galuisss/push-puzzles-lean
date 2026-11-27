/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.OrderedSlots
public import Mathlib.Data.Int.Interval

/-! The ordered slots of three fixed-length consecutive box trains. -/

public section
namespace PushPuzzle.PushS.RowLabels


/-- Three integer-coordinate trains, described by their first coordinates and lengths. -/
structure ThreeBlocks where
  first : ℤ
  middle : ℤ
  last : ℤ
  firstLength : ℕ
  middleLength : ℕ
  lastLength : ℕ

namespace ThreeBlocks

/-- Total number of occupied slots. -/
@[expose] def size (b : ThreeBlocks) : ℕ := b.firstLength + b.middleLength + b.lastLength

/-- The three trains occur in their declared order without overlap. -/
@[expose] def Separated (b : ThreeBlocks) : Prop :=
  b.first + b.firstLength ≤ b.middle ∧ b.middle + b.middleLength ≤ b.last

/-- All occupied coordinate slots of the three trains. -/
@[expose] def slots (b : ThreeBlocks) : Finset ℤ :=
  Finset.Ico b.first (b.first + b.firstLength) ∪
    Finset.Ico b.middle (b.middle + b.middleLength) ∪ Finset.Ico b.last (b.last + b.lastLength)

/-- Enumerate the first train, then the middle train, then the last train. -/
@[expose] def point (b : ThreeBlocks) (i : Fin b.size) : ℤ :=
  if i.val < b.firstLength then b.first + i.val
  else if i.val < b.firstLength + b.middleLength then b.middle + (i.val - b.firstLength : ℕ)
  else b.last + (i.val - (b.firstLength + b.middleLength) : ℕ)

/-- Membership in the train slots is membership in one of the three half-open intervals. -/
theorem mem_slots (b : ThreeBlocks) (x : ℤ) : x ∈ b.slots ↔
    (b.first ≤ x ∧ x < b.first + b.firstLength) ∨
      (b.middle ≤ x ∧ x < b.middle + b.middleLength) ∨
      (b.last ≤ x ∧ x < b.last + b.lastLength) := by
  simp only [slots, Finset.mem_union, Finset.mem_Ico]
  tauto

/-- All slots of ordered trains lie between the first start and the last end. -/
theorem slots_bounds (b : ThreeBlocks) (hb : b.Separated) {x : ℤ} (hx : x ∈ b.slots) :
    b.first ≤ x ∧ x < b.last + b.lastLength := by
  obtain ⟨hfirst, hmiddle⟩ := hb
  rcases (b.mem_slots x).mp hx with hx | hx | hx <;> omega

/-- Every enumerated coordinate lies in its train interval. -/
theorem point_mem (b : ThreeBlocks) (i : Fin b.size) : b.point i ∈ b.slots := by
  rw [mem_slots]
  have hi := i.isLt
  dsimp only [size] at hi
  unfold point
  split_ifs <;> omega

/-- The enumeration contains every occupied coordinate. -/
theorem exists_point (b : ThreeBlocks) {x : ℤ} (hx : x ∈ b.slots) : ∃ i, b.point i = x := by
  rcases (b.mem_slots x).mp hx with hx | hx | hx
  · have hc : ((x - b.first).toNat : ℤ) = x - b.first := Int.toNat_of_nonneg (by omega)
    let i : Fin b.size := ⟨(x - b.first).toNat, by dsimp only [size]; omega⟩
    refine ⟨i, ?_⟩
    dsimp only [point, i]
    split_ifs <;> omega
  · have hc : ((x - b.middle).toNat : ℤ) = x - b.middle := Int.toNat_of_nonneg (by omega)
    let i : Fin b.size := ⟨b.firstLength + (x - b.middle).toNat, by dsimp only [size]; omega⟩
    refine ⟨i, ?_⟩
    dsimp only [point, i]
    split_ifs <;> omega
  · have hc : ((x - b.last).toNat : ℤ) = x - b.last := Int.toNat_of_nonneg (by omega)
    let i : Fin b.size := ⟨b.firstLength + b.middleLength + (x - b.last).toNat, by dsimp only [size]; omega⟩
    refine ⟨i, ?_⟩
    dsimp only [point, i]
    split_ifs <;> omega

/-- Nonoverlapping ordered trains have a strictly increasing slot enumeration. -/
theorem strictMono_point (b : ThreeBlocks) (hb : b.Separated) : StrictMono b.point := by
  intro i j hij
  obtain ⟨hfirst, hmiddle⟩ := hb
  have hi := i.isLt
  have hj := j.isLt
  dsimp only [size] at hi hj
  unfold point
  split_ifs <;> omega

/-- The train enumeration covers exactly its occupied coordinate slots. -/
theorem slots_eq_image_point (b : ThreeBlocks) : b.slots = Finset.univ.image b.point := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, rfl⟩ := b.exists_point hx
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro hx
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
    exact b.point_mem i

/-- Ordered train slots have exactly the prescribed total length. -/
theorem card_slots (b : ThreeBlocks) (hb : b.Separated) : b.slots.card = b.size := by
  rw [b.slots_eq_image_point, Finset.card_image_of_injective Finset.univ (b.strictMono_point hb).injective,
    Finset.card_univ, Fintype.card_fin]

/-- The standard ordered finite-slot enumeration agrees with the three actual train blocks. -/
theorem orderEmbOfFin_eq_point (b : ThreeBlocks) (hb : b.Separated) :
    b.slots.orderEmbOfFin (b.card_slots hb) = b.point := by
  exact (Finset.orderEmbOfFin_unique (b.card_slots hb) b.point_mem (b.strictMono_point hb)).symm

/-- An ordered line state with these three occupied intervals has the explicit train coordinates. -/
theorem ordered_coordinates {w h : ℕ} {axis : PushFS.Direction} {lane : ℕ}
    (b : ThreeBlocks) (hb : b.Separated) (S : OrderedLineState b.size w h axis lane)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) (i : Fin b.size) :
    axis.position (S.position i) = b.point i := by
  have hmem (j : Fin b.size) : axis.position (S.position j) ∈ b.slots := by
    rw [← hslots]
    exact Finset.mem_image.mpr ⟨S.position j, S.toLineState.position_mem j, rfl⟩
  have he := Finset.orderEmbOfFin_unique (b.card_slots hb) hmem S.ordered
  exact congrFun (he.trans (b.orderEmbOfFin_eq_point hb)) i

end ThreeBlocks
end PushPuzzle.PushS.RowLabels

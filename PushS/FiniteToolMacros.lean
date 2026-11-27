/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTools
public import PushS.FiniteWalls
import Mathlib.Tactic.FinCases

/-! Actual single-push macros and continuous player walks for thick tools. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- Independent left and right phases record the parity macro's propagation frontier. -/
def parityMixedCell (w : ℕ) (a b : Bool) : ParityLabel → Cell (side w) (side w)
  | .left => parityCell w a .left
  | .right => parityCell w b .right
  | .predecessor => parityCell w false .predecessor
  | .successor => parityCell w false .successor

def parityMixedBoxes (w : ℕ) (a b : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (parityMixedCell w a b)

private theorem parityMixedBoxes_same (w : ℕ) (q : Bool) :
    parityMixedBoxes w q q = parityBoxes w q := rfl

private theorem parityMixedBoxes_disjoint (w : ℕ) (a b : Bool) :
    Disjoint (parityMixedBoxes w a b) (parityWalls w) := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  cases l <;> exact parityCell_not_wall w _ _

theorem parityMixedCell_injective (w : ℕ) (a b : Bool) :
    Function.Injective (parityMixedCell w a b) := by
  intro i j he
  have h := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hm := paritySpan_bounds w
  cases i <;> cases j <;>
    dsimp [parityMixedCell, parityCell, parityPoint, radius] at h <;> first | rfl | omega

private theorem image_relocate {α β : Type} [Fintype α] [DecidableEq α] [DecidableEq β]
    (f g : α → β) (hf : Function.Injective f) (a : α)
    (hrest : ∀ i, i ≠ a → g i = f i) :
    insert (g a) ((Finset.univ.image f).erase (f a)) = Finset.univ.image g := by
  ext p
  constructor
  · intro hp
    rcases Finset.mem_insert.mp hp with rfl | hp
    · exact Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩
    · obtain ⟨hne, hp⟩ := Finset.mem_erase.mp hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      have hi : i ≠ a := fun hh => hne (congrArg f hh)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hrest i hi⟩
  · intro hp
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
    by_cases hi : i = a
    · exact Finset.mem_insert.mpr (Or.inl (congrArg g hi))
    · apply Finset.mem_insert_of_mem
      rw [hrest i hi]
      exact Finset.mem_erase.mpr ⟨fun he => hi (hf he),
        Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

private theorem parity_right_update (w : ℕ) (a : Bool) :
    insert (parityCell w true .right)
      ((parityMixedBoxes w a false).erase (parityCell w false .right)) =
      parityMixedBoxes w a true := by
  apply image_relocate (parityMixedCell w a false) (parityMixedCell w a true)
    (parityMixedCell_injective w a false) .right
  intro l hl
  cases l <;> first | rfl | exact False.elim (hl rfl)

private theorem parity_left_update (w : ℕ) (b : Bool) :
    insert (parityCell w true .left)
      ((parityMixedBoxes w false b).erase (parityCell w false .left)) =
      parityMixedBoxes w true b := by
  apply image_relocate (parityMixedCell w false b) (parityMixedCell w true b)
    (parityMixedCell_injective w false b) .left
  intro l hl
  cases l <;> first | rfl | exact False.elim (hl rfl)

/-- Right support, right old slot, two roof corners, left support, left old slot. -/
def parityRoute (w : ℕ) (i : Fin 6) : Cell (side w) (side w) :=
  (⟨match i.val with
      | 0 => radius w+paritySpan w+1
      | 1 | 2 => radius w+paritySpan w+2
      | 3 | 4 => radius w-1
      | _ => radius w, by
      have hm := paritySpan_bounds w
      fin_cases i <;> simp [side, radius] <;> omega⟩,
   ⟨if i.val = 2 ∨ i.val = 3 then radius w-w-1 else radius w, by
      unfold side radius
      split <;> omega⟩)

theorem parityRoute_not_wall (w : ℕ) (i : Fin 6) :
    parityRoute w i ∉ parityWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := ((parityRectangle w j).mem_cells _ _ _).mp hj
  fin_cases i <;> fin_cases j <;>
    simp [parityRoute, parityRectangle, radius] at hj' <;> omega

private theorem parityRoute_not_box (w : ℕ) (a b : Bool) (i : Fin 6)
    (hi : i.val = 0 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4) :
    parityRoute w i ∉ parityMixedBoxes w a b := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hy := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hm := paritySpan_bounds w
  fin_cases i <;> cases l <;>
    simp [parityMixedCell, parityCell, parityPoint, parityRoute, radius] at hx hy hi <;> omega

private theorem parityRoute_right_old (w : ℕ) :
    parityRoute w 1 = parityCell w false .right := rfl

private theorem parityRoute_left_old (w : ℕ) :
    parityRoute w 5 = parityCell w false .left := rfl

theorem parity_roof_walk_free (w : ℕ) (p : Cell (side w) (side w))
    (hy : p.2.val ≤ radius w)
    (hx : p.1.val = radius w + paritySpan w + 2 ∨ p.1.val = radius w-1 ∨
      p.2.val < radius w-w ∨ p.1.val = radius w+1 ∨
        p.1.val = radius w+paritySpan w+4) :
    Free ⟨parityWalls w, parityBoxes w true⟩ (parityMixedBoxes w false true) p := by
  constructor
  · intro hp
    dsimp [radius] at hx hy
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hp
    have hi' := ((parityRectangle w i).mem_cells _ _ _).mp hi
    fin_cases i <;> simp [parityRectangle, radius] at hi' <;> omega
  · intro hp
    obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
    have heX := congrArg (fun z : Cell (side w) (side w) => z.1.val) he
    have heY := congrArg (fun z : Cell (side w) (side w) => z.2.val) he
    have hm := paritySpan_bounds w
    cases l <;> dsimp [parityMixedCell, parityCell, parityPoint] at heX heY <;>
      dsimp [radius] at hx hy heX heY <;> omega

/-- The three actual straight walks around the odd roof preserve the propagation frontier. -/
private theorem parity_roof_walk (w : ℕ) :
    Reachable ⟨parityWalls w, parityBoxes w true⟩ (some 1)
      ⟨parityRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityRoute w 4, parityMixedBoxes w false true⟩ := by
  let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w true⟩
  have hd : Disjoint (parityMixedBoxes w false true) B.walls :=
    parityMixedBoxes_disjoint w false true
  have h12 : Reachable B (some 1)
      ⟨parityRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityRoute w 2, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_roof_walk_free w
    · simp at hy hy' ⊢; omega
    · exact Or.inl rfl
  have h23 : Reachable B (some 1)
      ⟨parityRoute w 2, parityMixedBoxes w false true⟩
      ⟨parityRoute w 3, parityMixedBoxes w false true⟩ := by
    apply walk_horizontal hd
    intro x _ _
    apply parity_roof_walk_free w
    · simp; omega
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      simp [radius]
      omega
  have h34 : Reachable B (some 1)
      ⟨parityRoute w 3, parityMixedBoxes w false true⟩
      ⟨parityRoute w 4, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_roof_walk_free w
    · simp at hy hy' ⊢; omega
    · exact Or.inr (Or.inl rfl)
  exact h12.trans (h23.trans h34)

private theorem parity_right_destination_empty (w : ℕ) (a : Bool) :
    parityCell w true .right ∉ parityMixedBoxes w a false := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have ha := Bool.toNat_le a
  have hm := paritySpan_bounds w
  cases l <;> simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

private theorem parity_left_destination_empty (w : ℕ) (b : Bool) :
    parityCell w true .left ∉ parityMixedBoxes w false b := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hb := Bool.toNat_le b
  have hm := paritySpan_bounds w
  cases l <;> simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

/-- The parity adapter's real two-push macro includes the complete walk around its odd roof. -/
private theorem parity_forward (w : ℕ) :
    Reachable ⟨parityWalls w, parityBoxes w true⟩ (some 1)
      ⟨parityRoute w 0, parityBoxes w false⟩ ⟨parityRoute w 5, parityBoxes w true⟩ := by
  let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w true⟩
  have hE : Move B (some 1) .east
      ⟨parityRoute w 0, parityMixedBoxes w false false⟩
      ⟨parityRoute w 1, parityMixedBoxes w false true⟩ := by
    rw [parityRoute_right_old, ← parity_right_update w false]
    apply Move.single_iff.mpr
    apply SingleMoveView.push
    · exact ⟨parityRoute_not_wall w 0, parityMixedBoxes_disjoint w false false,
        parityRoute_not_box w false false 0 (by decide)⟩
    · simp [Adjacent, parityRoute, parityCell, parityPoint, Nat.add_assoc]
    · exact Finset.mem_image.mpr ⟨.right, Finset.mem_univ _, rfl⟩
    · simp [Adjacent, parityCell, parityPoint, Nat.add_assoc]
    · exact parityCell_not_wall w true .right
    · exact parity_right_destination_empty w false
  have hD : Move B (some 1) .east
      ⟨parityRoute w 4, parityMixedBoxes w false true⟩
      ⟨parityRoute w 5, parityMixedBoxes w true true⟩ := by
    rw [parityRoute_left_old, ← parity_left_update w true]
    apply Move.single_iff.mpr
    apply SingleMoveView.push
    · exact ⟨parityRoute_not_wall w 4, parityMixedBoxes_disjoint w false true,
        parityRoute_not_box w false true 4 (by decide)⟩
    · simp [Adjacent, parityRoute, parityCell, parityPoint, radius]
    · exact Finset.mem_image.mpr ⟨.left, Finset.mem_univ _, rfl⟩
    · simp [Adjacent, parityCell, parityPoint]
    · exact parityCell_not_wall w true .left
    · exact parity_left_destination_empty w true
  change Reachable B (some 1) _ _
  rw [← parityMixedBoxes_same w false, ← parityMixedBoxes_same w true]
  exact (Relation.ReflTransGen.single ⟨.east, hE⟩).trans ((parity_roof_walk w).tail ⟨.east, hD⟩)

private theorem parity_right_reverse (w : ℕ) (a : Bool) :
    insert (parityCell w false .right)
      ((parityMixedBoxes w a true).erase (parityCell w true .right)) =
      parityMixedBoxes w a false := by
  apply image_relocate (parityMixedCell w a true) (parityMixedCell w a false)
    (parityMixedCell_injective w a true) .right
  intro l hl
  cases l <;> first | rfl | exact False.elim (hl rfl)

private theorem parity_left_reverse (w : ℕ) (b : Bool) :
    insert (parityCell w false .left)
      ((parityMixedBoxes w true b).erase (parityCell w true .left)) =
      parityMixedBoxes w false b := by
  apply image_relocate (parityMixedCell w true b) (parityMixedCell w false b)
    (parityMixedCell_injective w true b) .left
  intro l hl
  cases l <;> first | rfl | exact False.elim (hl rfl)

private theorem parity_right_old_empty (w : ℕ) (a : Bool) :
    parityCell w false .right ∉ parityMixedBoxes w a true := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have ha := Bool.toNat_le a
  have hm := paritySpan_bounds w
  cases l <;> simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

private theorem parity_left_old_empty (w : ℕ) (b : Bool) :
    parityCell w false .left ∉ parityMixedBoxes w true b := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hb := Bool.toNat_le b
  have hm := paritySpan_bounds w
  cases l <;> simp [parityMixedCell, parityCell, parityPoint, radius] at hx <;> omega

/-- Left support, left old slot, two roof corners, right support, right old slot. -/
def parityBackwardRoute (w : ℕ) (i : Fin 6) : Cell (side w) (side w) :=
  (⟨match i.val with
      | 0 => radius w+2
      | 1 | 2 => radius w+1
      | 3 | 4 => radius w+paritySpan w+4
      | _ => radius w+paritySpan w+3, by
      have hm := paritySpan_bounds w
      fin_cases i <;> simp [side, radius] <;> omega⟩,
   ⟨if i.val = 2 ∨ i.val = 3 then radius w-w-1 else radius w, by
      unfold side radius
      split <;> omega⟩)

theorem parityBackwardRoute_not_wall (w : ℕ) (i : Fin 6) :
    parityBackwardRoute w i ∉ parityWalls w := by
  intro hp
  obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hp
  have hj' := ((parityRectangle w j).mem_cells _ _ _).mp hj
  fin_cases i <;> fin_cases j <;>
    simp [parityBackwardRoute, parityRectangle, radius] at hj' <;> omega

private theorem parityBackwardRoute_not_box (w : ℕ) (a b : Bool) (i : Fin 6)
    (hi : i.val = 0 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4) :
    parityBackwardRoute w i ∉ parityMixedBoxes w a b := by
  intro hp
  obtain ⟨l, _, he⟩ := Finset.mem_image.mp hp
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hy := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  have hm := paritySpan_bounds w
  fin_cases i <;> cases l <;>
    simp [parityMixedCell, parityCell, parityPoint, parityBackwardRoute, radius] at hx hy hi <;> omega

private theorem parity_backward_roof_walk (w : ℕ) :
    Reachable ⟨parityWalls w, parityBoxes w false⟩ (some 1)
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 4, parityMixedBoxes w false true⟩ := by
  let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w false⟩
  have hd : Disjoint (parityMixedBoxes w false true) B.walls :=
    parityMixedBoxes_disjoint w false true
  have h12 : Reachable B (some 1)
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 2, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_roof_walk_free w
    · simp at hy hy' ⊢; omega
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
  have h23 : Reachable B (some 1)
      ⟨parityBackwardRoute w 2, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 3, parityMixedBoxes w false true⟩ := by
    apply walk_horizontal hd
    intro x _ _
    apply parity_roof_walk_free w
    · simp; omega
    · apply Or.inr ∘ Or.inr ∘ Or.inl
      simp [radius]
      omega
  have h34 : Reachable B (some 1)
      ⟨parityBackwardRoute w 3, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 4, parityMixedBoxes w false true⟩ := by
    apply walk_vertical hd
    intro y hy hy'
    apply parity_roof_walk_free w
    · simp at hy hy' ⊢; omega
    · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
  exact h12.trans (h23.trans h34)

/-- Reverse propagation uses two single pushes and the actual route around the roof. -/
private theorem parity_backward (w : ℕ) :
    Reachable ⟨parityWalls w, parityBoxes w false⟩ (some 1)
      ⟨parityBackwardRoute w 0, parityBoxes w true⟩
      ⟨parityBackwardRoute w 5, parityBoxes w false⟩ := by
  let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w false⟩
  have hD : Move B (some 1) .west
      ⟨parityBackwardRoute w 0, parityMixedBoxes w true true⟩
      ⟨parityBackwardRoute w 1, parityMixedBoxes w false true⟩ := by
    change Move B (some 1) .west _ ⟨parityCell w true .left, _⟩
    rw [← parity_left_reverse w true]
    apply Move.single_iff.mpr
    apply SingleMoveView.push
    · exact ⟨parityBackwardRoute_not_wall w 0, parityMixedBoxes_disjoint w true true,
        parityBackwardRoute_not_box w true true 0 (by decide)⟩
    · simp [Adjacent, parityBackwardRoute, parityCell, parityPoint, Nat.add_assoc]
    · exact Finset.mem_image.mpr ⟨.left, Finset.mem_univ _, rfl⟩
    · simp [Adjacent, parityCell, parityPoint]
    · exact parityCell_not_wall w false .left
    · exact parity_left_old_empty w true
  have hE : Move B (some 1) .west
      ⟨parityBackwardRoute w 4, parityMixedBoxes w false true⟩
      ⟨parityBackwardRoute w 5, parityMixedBoxes w false false⟩ := by
    change Move B (some 1) .west _ ⟨parityCell w true .right, _⟩
    rw [← parity_right_reverse w false]
    apply Move.single_iff.mpr
    apply SingleMoveView.push
    · exact ⟨parityBackwardRoute_not_wall w 4, parityMixedBoxes_disjoint w false true,
        parityBackwardRoute_not_box w false true 4 (by decide)⟩
    · simp [Adjacent, parityBackwardRoute, parityCell, parityPoint, Nat.add_assoc]
    · exact Finset.mem_image.mpr ⟨.right, Finset.mem_univ _, rfl⟩
    · simp [Adjacent, parityCell, parityPoint, Nat.add_assoc]
    · exact parityCell_not_wall w false .right
    · exact parity_right_old_empty w false
  change Reachable B (some 1) _ _
  rw [← parityMixedBoxes_same w true, ← parityMixedBoxes_same w false]
  exact (Relation.ReflTransGen.single ⟨.west, hD⟩).trans
    ((parity_backward_roof_walk w).tail ⟨.west, hE⟩)

/-- The same forward macro works after all thickness-`k+1` walls become ordinary boxes. -/
theorem parity_forward_wallFree (k : ℕ) (hk : 1 ≤ k) :
    let w := k+1
    let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w true⟩
    Reachable (FiniteWalls.board B) (some k)
      (FiniteWalls.fill B ⟨parityRoute w 0, parityBoxes w false⟩)
      (FiniteWalls.fill B ⟨parityRoute w 5, parityBoxes w true⟩) :=
  FiniteWalls.reachable_fill ((parity_forward (k+1)).mono (fun _ hn => Nat.le_trans hn hk))

/-- The reverse macro preserves all wall boxes and both actual exterior neighbors. -/
theorem parity_backward_wallFree (k : ℕ) (hk : 1 ≤ k) :
    let w := k+1
    let B : Board (side w) (side w) := ⟨parityWalls w, parityBoxes w false⟩
    Reachable (FiniteWalls.board B) (some k)
      (FiniteWalls.fill B ⟨parityBackwardRoute w 0, parityBoxes w true⟩)
      (FiniteWalls.fill B ⟨parityBackwardRoute w 5, parityBoxes w false⟩) :=
  FiniteWalls.reachable_fill ((parity_backward (k+1)).mono (fun _ hn => Nat.le_trans hn hk))

end PushPuzzle.PushS.FiniteTools

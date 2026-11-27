/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteFlipMacros
public import PushS.FiniteTurnMacros

/-! Sparse normal inventories and exact physical slot connectivity for finite-push tools. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS

/-- Every pair of normal flip boxes, including the exterior neighbors, is nonadjacent. -/
theorem flipBoxes_sparse (w : ℕ) (hw : 2 ≤ w) (q : Bool)
    {p r : Cell (side w) (side w)} (hp : p ∈ flipBoxes w q) (hr : r ∈ flipBoxes w q)
    (d : Direction) : ¬ Adjacent d p r := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
  intro ha
  have hq := Bool.toNat_le q
  cases d <;> cases i <;> cases j <;>
    simp [Adjacent, flipCell, flipPoint, radius] at ha <;> omega

theorem parityBoxes_sparse (w : ℕ) (q : Bool)
    {p r : Cell (side w) (side w)} (hp : p ∈ parityBoxes w q) (hr : r ∈ parityBoxes w q)
    (d : Direction) : ¬ Adjacent d p r := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
  intro ha
  have hq := Bool.toNat_le q
  have hm := paritySpan_bounds w
  cases d <;> cases i <;> cases j <;>
    simp [Adjacent, parityCell, parityPoint, radius] at ha <;> omega

theorem turnBoxes_sparse (w : ℕ) (q : Bool)
    {p r : Cell (side w) (side w)} (hp : p ∈ turnBoxes w q) (hr : r ∈ turnBoxes w q)
    (d : Direction) : ¬ Adjacent d p r := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hr
  intro ha
  have hq := Bool.toNat_le q
  cases d <;> cases i <;> cases j <;>
    simp [Adjacent, turnMixedCell, turnMixedPoint, radius] at ha <;> omega

end PushPuzzle.PushS.FiniteTools

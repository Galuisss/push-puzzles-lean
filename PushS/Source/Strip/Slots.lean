/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Init
public import Mathlib.Data.Finset.Sort
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.Finite

/-!
# Explicit slots within a bounded row

A placement records a row and a slot in that row. For finite indexed data, slots are computed
by scanning the increasing list of indices in the same row. The result retains the given rows.

## Main definitions

* `PushPuzzle.NCL.Strip.Placement`: injective row/slot coordinates with a fixed slot capacity.
* `PushPuzzle.NCL.Strip.Placement.ofRows`: actual slot allocation for a bounded finite row array.

## Main results

* `PushPuzzle.NCL.Strip.Placement.address_injective`: the flattened panel address identifies the input item.
-/

public section

namespace PushPuzzle.NCL.Strip

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- A row and one of a fixed number of slots, jointly identifying each item. -/
structure Placement (α : Type*) (capacity : ℕ) where
  /-- Longitudinal panel containing the item. -/
  row : α → ℕ
  /-- Index of the item within its panel. -/
  slot : α → Fin capacity
  /-- Distinct items have distinct row/slot coordinates. -/
  injective : Function.Injective (fun a => (row a, slot a))

namespace Placement

open Cslib.Complexity Cslib.Complexity.NCL

variable {α : Type*} {capacity : ℕ}

/-- Flattened address of an item, using exactly `capacity` slots per panel. -/
@[expose] def address (P : Placement α capacity) (a : α) : ℕ :=
  capacity * P.row a + P.slot a

/-- Flattening the finite slots preserves the original item's identity. -/
theorem address_injective (P : Placement α capacity) : Function.Injective P.address := by
  intro a b h
  have ha := (P.slot a).isLt
  have hb := (P.slot b).isLt
  have hr : P.row a = P.row b := by
    simp only [address] at h
    rcases lt_trichotomy (P.row a) (P.row b) with hr | hr | hr
    · have hh := Nat.mul_le_mul_left capacity (show P.row a + 1 ≤ P.row b from hr)
      simp only [Nat.mul_add, Nat.mul_one] at hh
      omega
    · exact hr
    · have hh := Nat.mul_le_mul_left capacity (show P.row b + 1 ≤ P.row a from hr)
      simp only [Nat.mul_add, Nat.mul_one] at hh
      omega
  apply P.injective
  apply Prod.ext hr
  apply Fin.ext
  change (P.slot a).val = (P.slot b).val
  simp only [address, hr] at h
  omega

/-- Each row contains at most as many items as there are slots. -/
theorem card_row_le (P : Placement α capacity) (r : ℕ) :
    Nat.card {a // P.row a = r} ≤ capacity := by
  let f : {a // P.row a = r} → Fin capacity := fun a => P.slot a.val
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    apply P.injective
    exact Prod.ext (a.property.trans b.property.symm) h
  simpa only [Nat.card_fin] using Nat.card_le_card_of_injective f hf

/-- The increasing list of original indices in one row. -/
@[expose] def rowIndices {n : ℕ} (rows : Fin n → ℕ) (r : ℕ) : List (Fin n) :=
  (Finset.univ.filter (fun i => rows i = r)).sort

private theorem mem_rowIndices {n : ℕ} (rows : Fin n → ℕ) (i : Fin n) :
    i ∈ rowIndices rows (rows i) := by simp [rowIndices]

/-- Allocate slots by the actual sorted finite list of indices in the same row. -/
@[expose] def ofRows {n capacity : ℕ} (rows : Fin n → ℕ)
    (bound : ∀ r, Fintype.card {i // rows i = r} ≤ capacity) :
    Placement (Fin n) capacity where
  row := rows
  slot i := ⟨(rowIndices rows (rows i)).idxOf i, by
    have hi := List.idxOf_lt_length_of_mem
      (mem_rowIndices rows i)
    simp only [rowIndices, Finset.length_sort] at hi
    have hb := bound (rows i)
    rw [Fintype.card_subtype] at hb
    exact hi.trans_le hb⟩
  injective := by
    intro i j h
    have hr := congrArg Prod.fst h
    have hs := congrArg (fun p : ℕ × Fin capacity => p.2.val) h
    change (rowIndices rows (rows i)).idxOf i = (rowIndices rows (rows j)).idxOf j at hs
    change rows i = rows j at hr
    rw [hr] at hs
    apply (List.idxOf_inj ?_).mp hs
    exact hr ▸ mem_rowIndices rows i

/-- Slot allocation preserves the supplied row function definitionally. -/
@[simp] theorem ofRows_row {n capacity : ℕ} (rows : Fin n → ℕ)
    (bound : ∀ r, Fintype.card {i // rows i = r} ≤ capacity) (i : Fin n) :
    (ofRows rows bound).row i = rows i := rfl

end Placement
end PushPuzzle.NCL.Strip

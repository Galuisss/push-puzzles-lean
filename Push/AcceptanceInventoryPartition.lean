/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card

/-! Conserved total inventory saturates every disjoint local account above its original count. -/

public section
namespace PushPuzzle.Push.AcceptanceInventory

open scoped BigOperators

/-- Disjoint terminal accounts covering their original total cannot exceed any original local inventory. -/
theorem partition_card_eq {ι α : Type*} [Fintype ι] [DecidableEq α]
    (initial terminal : Finset α) (before after : ι → Finset α)
    (cover : initial ⊆ Finset.univ.biUnion before) (contained : ∀ i, after i ⊆ terminal)
    (disjoint : Pairwise fun i j => Disjoint (after i) (after j))
    (lower : ∀ i, (before i).card ≤ (after i).card) (total : initial.card = terminal.card) (i : ι) :
    (after i).card = (before i).card := by
  classical
  have original : initial.card ≤ ∑ j, (before j).card :=
    (Finset.card_le_card cover).trans Finset.card_biUnion_le
  have sub : Finset.univ.biUnion after ⊆ terminal := by
    intro q hq
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hq
    exact contained j hj
  have pairwise : Set.PairwiseDisjoint (↑(Finset.univ : Finset ι)) after :=
    fun j _ k _ hne => disjoint hne
  have final := Finset.card_le_card sub
  rw [Finset.card_biUnion pairwise] at final
  have same : ∑ j, (before j).card = ∑ j, (after j).card := by
    have monotone := Finset.sum_le_sum (s := Finset.univ) (fun j _ => lower j)
    omega
  exact ((Finset.sum_eq_sum_iff_of_le (fun j _ => lower j)).mp same i (Finset.mem_univ _)).symm

end PushPuzzle.Push.AcceptanceInventory

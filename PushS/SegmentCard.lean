/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortSegmentInventory

/-!
# Cardinalities of closed lattice segments

The existing integer-trace union counts a horizontal or vertical segment once at each
integer coordinate. These formulas are used by the actual physical signal inventories.
-/

public section

namespace PushPuzzle.PushS.SegmentRecipe


open PushFS.Reduction

/-- A closed horizontal segment has one cell for every integer coordinate between its ends. -/
theorem pointHoles_horizontal_card (x u y : ℕ) :
    (pointHoles [⟨(x, y), (u, y)⟩]).card = max x u - min x u + 1 := by
  have he : pointHoles [⟨(x, y), (u, y)⟩] =
      (Finset.range (max x u - min x u + 1)).image (fun i => (min x u + i, y)) := by
    ext q
    simp [pointHoles, Segment.cells]
  rw [he, Finset.card_image_of_injective]
  · exact Finset.card_range _
  · intro i j hij
    exact Nat.add_left_cancel (congrArg Prod.fst hij)

/-- A closed vertical segment has one cell for every integer coordinate between its ends. -/
theorem pointHoles_vertical_card (x y v : ℕ) :
    (pointHoles [⟨(x, y), (x, v)⟩]).card = max y v - min y v + 1 := by
  by_cases hy : y = v
  · subst v
    simpa using pointHoles_horizontal_card x x y
  · have he : pointHoles [⟨(x, y), (x, v)⟩] =
        (Finset.range (max y v - min y v + 1)).image (fun i => (x, min y v + i)) := by
      ext q
      simp [pointHoles, Segment.cells, hy]
    rw [he, Finset.card_image_of_injective]
    · exact Finset.card_range _
    · intro i j hij
      exact Nat.add_left_cancel (congrArg Prod.snd hij)

/-- Membership in the actual trace of one horizontal segment. -/
theorem mem_pointHoles_horizontal (x u y : ℕ) (q : ℕ × ℕ) :
    q ∈ pointHoles [⟨(x, y), (u, y)⟩] ↔ q.2 = y ∧ min x u ≤ q.1 ∧ q.1 ≤ max x u := by
  simp only [mem_pointHoles, List.mem_singleton, exists_eq_left, Segment.Contains,
    Nat.min_self, Nat.max_self, true_and]
  omega

/-- Membership in the actual trace of one vertical segment. -/
theorem mem_pointHoles_vertical (x y v : ℕ) (q : ℕ × ℕ) :
    q ∈ pointHoles [⟨(x, y), (x, v)⟩] ↔ q.1 = x ∧ min y v ≤ q.2 ∧ q.2 ≤ max y v := by
  simp only [mem_pointHoles, List.mem_singleton, exists_eq_left, Segment.Contains,
    Nat.min_self, Nat.max_self, true_and]
  omega

end PushPuzzle.PushS.SegmentRecipe

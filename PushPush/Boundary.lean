/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide

/-! Boundary permanence and box-supported stopping on successful prefixes. -/

@[expose] public section
namespace PushPuzzle.PushPush

open PushFS (Cell Direction Adjacent State)

variable {w h n k : ℕ} {d : Direction} {s t : State w h}

/-- Cells on one of the four true edges of the rectangle. -/
def Boundary (p : Cell w h) : Prop :=
  p.1.val = 0 ∨ p.1.val + 1 = w ∨ p.2.val = 0 ∨ p.2.val + 1 = h

/-- No box touches the true boundary. -/
def Interior (s : State w h) : Prop := ∀ p ∈ s.boxes, ¬ Boundary p

theorem Slide.boundary_after (r : Slide d s n k) (i : Fin n)
    (hb : Boundary (r.cell ⟨i.val + 1, by omega⟩)) :
    Boundary (r.cell ⟨k + i.val + 1, by omega⟩) := by
  have hp := r.position ⟨i.val + 1, by omega⟩
  have hq := r.position ⟨k + i.val + 1, by omega⟩
  have hl := r.lane ⟨i.val + 1, by omega⟩
  have hm := r.lane ⟨k + i.val + 1, by omega⟩
  cases d <;> simp only [Direction.position, Direction.lane] at hp hq hl hm <;>
    simp only [Boundary] at hb ⊢ <;> omega

/-- Once an edge contains a box, every later state still has an edge box. -/
theorem Move.interior_source (hm : Move d s t) (ht : Interior t) : Interior s := by
  cases hm with
  | walk _ _ _ hb => simpa only [Interior, hb] using ht
  | push _ _ _ r _ hb =>
    intro p hp hbound
    by_cases hm : p ∈ r.before
    · obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hm
      apply ht _ ?_ (r.boundary_after i hbound)
      rw [hb]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
    · apply ht p
      · rw [hb]
        exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hp, hm⟩)
      · exact hbound

theorem Reachable.interior_source (hr : Reachable s t) (ht : Interior t) : Interior s := by
  induction hr with
  | refl => exact ht
  | tail _ hm ih => exact ih (hm.choose_spec.interior_source ht)

/-- Every interior cell has a next cell in each direction. -/
theorem adjacent_exists_of_interior (p : Cell w h) (hp : ¬ Boundary p) (d : Direction) :
    ∃ q, Adjacent d p q := by
  simp only [Boundary, not_or] at hp
  cases d with
  | north => exact ⟨(p.1, ⟨p.2.val - 1, by omega⟩), rfl, by
      change p.2.val - 1 + 1 = p.2.val; omega⟩
  | east => exact ⟨(⟨p.1.val + 1, by omega⟩, p.2), rfl, rfl⟩
  | south => exact ⟨(p.1, ⟨p.2.val + 1, by omega⟩), rfl, rfl⟩
  | west => exact ⟨(⟨p.1.val - 1, by omega⟩, p.2), by
      change p.1.val - 1 + 1 = p.1.val; omega, rfl⟩

/-- A positive slide ending away from the boundary stops against an unchanged box. -/
theorem Slide.exists_stopper (r : Slide d s n k) (hn : 0 < n)
    (ht : ∀ p ∈ r.boxes, ¬ Boundary p) :
    ∃ q ∈ s.boxes, Adjacent d (r.cell ⟨n + k, by omega⟩) q := by
  have he : (⟨k + (n - 1) + 1, by omega⟩ : Fin (n + k + 1)) =
      ⟨n + k, by omega⟩ := Fin.ext (by change k + (n - 1) + 1 = n + k; omega)
  have hmem : r.cell ⟨n + k, by omega⟩ ∈ r.boxes := by
    apply Finset.mem_union_right
    exact Finset.mem_image.mpr ⟨⟨n - 1, by omega⟩, Finset.mem_univ _, by rw [he]⟩
  obtain ⟨q, hq⟩ := adjacent_exists_of_interior _ (ht _ hmem) d
  exact ⟨q, r.stopped q hq, hq⟩

end PushPuzzle.PushPush

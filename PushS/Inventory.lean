/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.RowInventory
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Successful balanced inventories eliminate all transfers across a one-way interface. -/

@[expose] public section
namespace PushPuzzle.PushS.Inventory

open PushFS
open scoped BigOperators

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ}
  {d : Direction} {s t : State w h} {R : Finset (Cell w h)}

/-- Number of boxes in the specified region. -/
def count (R : Finset (Cell w h)) (s : State w h) : ℕ :=
  ∑ p ∈ s.boxes, if p ∈ R then 1 else 0

theorem count_eq_card (R : Finset (Cell w h)) (s : State w h) :
    count R s = (s.boxes.filter fun p => p ∈ R).card := by
  simp [count, Finset.filter_mem_eq_inter]

theorem count_add_compl (R : Finset (Cell w h)) (s : State w h) :
    count R s + count Rᶜ s = s.boxes.card := by
  unfold count
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ _ ∈ s.boxes, (1 : ℕ) := by
      apply Finset.sum_congr rfl
      intro p _
      by_cases hp : p ∈ R <;> simp [hp]
    _ = s.boxes.card := by simp

/-- The first box and the first destination hole account for the entire region transfer. -/
theorem push_accounting {n : ℕ} (run : Run B d s n) (hn : 0 < n)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1))) :
    count R t + (if run.cell 1 ∈ R then 1 else 0) =
      count R s + (if run.cell ⟨n + 1, by omega⟩ ∈ R then 1 else 0) := by
  have hs := Finset.sum_erase_add s.boxes (fun p => if p ∈ R then 1 else 0)
    (run.first_occupied hn)
  change (∑ p ∈ s.boxes.erase (run.cell 1), if p ∈ R then 1 else 0) +
    (if run.cell 1 ∈ R then 1 else 0) = count R s at hs
  have ht : count R t = (if run.cell ⟨n + 1, by omega⟩ ∈ R then 1 else 0) +
      ∑ p ∈ s.boxes.erase (run.cell 1), if p ∈ R then 1 else 0 := by
    rw [count, hb, Finset.sum_insert (fun h => run.empty (Finset.mem_of_mem_erase h))]
  omega

/-- A real step whose pushes cannot transfer a box out of the region. -/
def ForwardStep (B : Board w h) (cap : Option ℕ) (R : Finset (Cell w h))
    (s t : State w h) : Prop :=
  Step B cap s t ∧ ∀ (d : Direction) (n : ℕ) (run : Run B d s n), 0 < n →
    t.player = run.cell 1 →
    t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)) →
    run.cell 1 ∈ R → run.cell ⟨n + 1, by omega⟩ ∈ R

theorem step_mono (hm : ForwardStep B cap R s t) : count R s ≤ count R t := by
  obtain ⟨d, hmove⟩ := hm.1
  cases hmove with
  | walk _ _ _ _ hb => simp only [count, hb, le_rfl]
  | @push n _ hn _ run hp hb =>
    have hc := push_accounting (R := R) run hn hb
    by_cases hq : run.cell 1 ∈ R
    · have hz := hm.2 d n run hn hp hb hq
      simp only [hq, hz, ite_true] at hc
      omega
    · simp only [hq, ite_false] at hc
      split at hc <;> omega

theorem reachable_mono (hr : Relation.ReflTransGen (ForwardStep B cap R) s t) :
    count R s ≤ count R t := by
  induction hr with
  | refl => exact le_rfl
  | tail _ hm ih => exact ih.trans (step_mono hm)

theorem reachable_forget (hr : Relation.ReflTransGen (ForwardStep B cap R) s t) :
    Reachable B cap s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hm ih => exact ih.tail hm.1

/-- The finite region of one complete row or column. -/
def line (axis : Direction) (lane : ℕ) : Finset (Cell w h) :=
  Finset.univ.filter fun p => axis.lane p = lane

end PushPuzzle.PushS.Inventory

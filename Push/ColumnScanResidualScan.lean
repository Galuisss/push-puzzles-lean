/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Scan

/-! Removing the southernmost current column hole is exactly one unit of the static reader. -/

public section
namespace PushPuzzle.Push.ReaderResidual

open PushFS

variable {w h : ℕ}

/-- Delete one actual hole, chosen at the southern end of its current column. -/
structure BottomPop (E F : Finset (Cell w h)) where
  cell : Cell w h
  present : cell ∈ E
  maximal : ∀ p ∈ E, p.1 = cell.1 → p.2.val ≤ cell.2.val
  result : F = E.erase cell

private theorem consume_one_max {α : Type*} [DecidableEq α] {cells : List α}
    {key : α → ℕ} {q : α} {E : Finset α} (hq : q ∈ cells) (hE : q ∈ E)
    (horder : cells.Pairwise (fun a b => key b < key a))
    (hmax : ∀ p ∈ E, p ∈ cells → key p ≤ key q) :
    Scan.consume cells 1 E = some (E.erase q) := by
  induction cells with
  | nil => simp only [List.not_mem_nil] at hq
  | cons a cells ih =>
    by_cases haq : a = q
    · subst a
      simp only [Scan.consume, ite_eq_left hE]
    · have hqt : q ∈ cells := (List.mem_cons.mp hq).resolve_left (Ne.symm haq)
      have hnot : a ∉ E := by
        intro ha
        have hh := (List.pairwise_cons.mp horder).1 q hqt
        have hm := hmax a ha (List.mem_cons_self ..)
        omega
      simp only [Scan.consume, ite_eq_right hnot]
      exact ih hqt (List.pairwise_cons.mp horder).2
        (fun p hp hc => hmax p hp (List.mem_cons_of_mem a hc))

private theorem south_line_order (lane : ℕ) :
    (Scan.lineCells (w := w) (h := h) .south lane).Pairwise
      (fun a b => b.2.val < a.2.val) := by
  simp only [Scan.lineCells]
  split
  · rw [List.pairwise_reverse, List.pairwise_ofFn]
    intro i j hij
    exact hij
  · exact List.Pairwise.nil

/-- The finite-set pop agrees with the static program's exact bottom-first consumption. -/
theorem BottomPop.read {E F : Finset (Cell w h)} (pop : BottomPop E F) :
    (Scan.Instruction.read .south pop.cell.1.val 1).eval E = some F := by
  rcases pop with ⟨q, hq, hmax, rfl⟩
  apply consume_one_max (key := fun p : Cell w h => p.2.val)
  · exact (Scan.mem_lineCells .south _ _).mpr rfl
  · exact hq
  · exact south_line_order _
  · intro p hp hline
    have hx : p.1.val = q.1.val := (Scan.mem_lineCells .south _ _).mp hline
    exact hmax p hp (Fin.ext hx)

end PushPuzzle.Push.ReaderResidual

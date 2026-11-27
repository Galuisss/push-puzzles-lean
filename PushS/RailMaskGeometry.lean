/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.RailMask

/-! Rectangular cell regions are closed under the occupied part of any straight push. -/

public section
namespace PushPuzzle.PushS.BoxMask


open PushFS

/-- The finite cell rectangle given by inclusive coordinate bounds. -/
@[expose] def rectangle {w h : ℕ} (xlo xhi ylo yhi : ℕ) : Finset (Cell w h) :=
  Finset.univ.filter fun q => xlo ≤ q.1.val ∧ q.1.val ≤ xhi ∧ ylo ≤ q.2.val ∧ q.2.val ≤ yhi

/-- Every occupied ray cell between two rectangle cells remains in the same rectangle. -/
theorem rectangle_runClosed {w h : ℕ} (xlo xhi ylo yhi : ℕ) :
    RunClosed (rectangle (w := w) (h := h) xlo xhi ylo yhi) := by
  intro B d s n run hn hfirst hlast i hi
  have hf := (Finset.mem_filter.mp hfirst).2
  have hl := (Finset.mem_filter.mp hlast).2
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hp1 := run.position 1
  have hpN := run.position ⟨n + 1, by omega⟩
  have hpi := run.position i
  have hx1 := run.lane 1
  have hxN := run.lane ⟨n + 1, by omega⟩
  have hxi := run.lane i
  have hb := i.isLt
  cases d <;> simp only [Direction.position, Direction.lane, Fin.val_one] at hp1 hpN hpi hx1 hxN hxi <;> omega

end PushPuzzle.PushS.BoxMask

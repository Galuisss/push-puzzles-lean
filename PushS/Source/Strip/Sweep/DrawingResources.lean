/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Resources
public import PushS.Source.Diagram.Word.Rows
public import PushS.Source.Diagram.Word.Geometric
import Mathlib.Algebra.Order.Group.Nat

/-!
# Actual layer heights of bounded-width word drawings

The existing orthogonal drawing uses the actual input and output stack sizes to set each layer's
height. A bound on all checked prefix stacks therefore bounds every actual layer, and the distance
between any fixed number of consecutive layers.

## Main results

* `PushPuzzle.NCL.Word.OrthogonalDrawing.heights_le`: every actual layer has bounded height.
* `PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset_add_le`: a fixed layer window has bounded geometric extent.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib

private theorem Slice.OrthogonalDrawing.wellTyped {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) : Word.WellTyped [sl] a b := by
  rw [← L.toWord_diagram]
  exact Diagram.wellTyped_toWord _ _

private theorem Slice.OrthogonalDrawing.height_le {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) {n : ℕ} (ha : a.length ≤ n) (hb : b.length ≤ n) :
    L.layout.height ≤ 4 * n + 6 := by
  have hs := congrArg List.length L.source_eq
  have ht := congrArg List.length L.target_eq
  simp only [List.length_append] at hs ht
  rw [GridLayout.Layer.height]
  omega

/-- A bound on the actual word's prefix stacks bounds each actual geometric layer's height. -/
theorem Word.OrthogonalDrawing.heights_le {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {n : ℕ} (h : Word.WidthBound w a n) :
    ∀ t ∈ Word.OrthogonalDrawing.heights D, t ≤ 4 * n + 6 := by
  induction D with
  | nil _ => simp [heights]
  | @cons sl w a b c layer rest ih =>
    have hl := Slice.OrthogonalDrawing.wellTyped layer
    have ha := h.start
    have hb : b.length ≤ n := h [sl] (List.prefix_append _ w) b hl
    have hr : PushPuzzle.NCL.Word.WidthBound w b n := h.of_append_right (u := [sl]) hl
    intro t ht
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Slice.OrthogonalDrawing.height_le layer ha hb
    · exact ih hr t ht

/-- Any fixed number of actual consecutive drawing layers occupies a fixed row interval. -/
theorem Word.OrthogonalDrawing.rowOffset_add_le {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {n : ℕ} (h : Word.WidthBound w a n) (i k : ℕ) :
    Word.OrthogonalDrawing.rowOffset D (i + k) ≤ Word.OrthogonalDrawing.rowOffset D i + k * (4 * n + 6) := by
  have hs := List.sum_le_length_nsmul (((Word.OrthogonalDrawing.heights D).drop i).take k) (4 * n + 6) (fun t ht =>
    Word.OrthogonalDrawing.heights_le D h t (List.mem_of_mem_drop (List.mem_of_mem_take ht)))
  simp only [nsmul_eq_mul, Nat.cast_id] at hs
  have hl := List.length_take_le k ((Word.OrthogonalDrawing.heights D).drop i)
  have hm := Nat.mul_le_mul_right (4 * n + 6) hl
  simp only [rowOffset, List.take_add, List.sum_append]
  omega

end PushPuzzle.NCL

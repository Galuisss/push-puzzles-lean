/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Orthogonal

import Mathlib.Algebra.Order.Group.Nat

/-! Layer rows for the internal strip drawing. -/

public section
namespace PushPuzzle.NCL
open Cslib.Complexity Cslib.Complexity.NCL

/-- The positive heights of the consecutive cell drawings. -/
@[expose] def Word.OrthogonalDrawing.heights {w : Word} {a b : List Color} :
    w.OrthogonalDrawing a b → List ℕ
  | .nil _ => []
  | .cons layer rest => layer.layout.height :: heights rest

/-- Every layer has positive height, so nonadjacent layers occupy separate row bands. -/
private theorem Word.OrthogonalDrawing.heights_pos {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) : ∀ h ∈ heights D, 0 < h := by
  induction D with
  | nil => simp [heights]
  | cons layer rest ih =>
    intro h hh
    rcases List.mem_cons.mp hh with rfl | hh
    · exact layer.layout.height_pos
    · exact ih _ hh

/-- The first row of layer `i` after placing all preceding layers above it. -/
@[expose] def Word.OrthogonalDrawing.rowOffset {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (i : ℕ) : ℕ := ((heights D).take i).sum

private theorem Word.OrthogonalDrawing.rowOffset_succ {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {i : ℕ} (hi : i < (heights D).length) :
    rowOffset D (i + 1) = rowOffset D i + (heights D)[i] := by
  simp only [rowOffset, List.take_succ_eq_append_getElem hi, List.sum_append,
    List.sum_singleton]

/-- An earlier layer ends before or at a later layer's first row. -/
private theorem Word.OrthogonalDrawing.band_separation {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {i j : ℕ} (hi : i < (heights D).length) (hij : i < j) :
    rowOffset D i + (heights D)[i] ≤ rowOffset D j := by
  rw [← rowOffset_succ D hi]
  exact List.monotone_sum_take (heights D) (by omega)

/-- Nonadjacent layers are separated by a positive row gap. -/
private theorem Word.OrthogonalDrawing.band_strict_separation {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {i j : ℕ} (hi : i < (heights D).length)
    (hj : j < (heights D).length) (hij : i + 1 < j) :
    rowOffset D i + (heights D)[i] < rowOffset D j := by
  have hin : i + 1 < (heights D).length := by omega
  have hp : 0 < (heights D)[i + 1] := heights_pos D _ (List.getElem_mem hin)
  have hs := band_separation D hin hij
  rw [← rowOffset_succ D hi]
  omega

/-- Distinct drawing layers can meet only at the common row of consecutive layers.
On this row both layers use the same ordered boundary ports, in columns `4 * i`. -/
theorem Word.OrthogonalDrawing.band_intersection {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {i j y : ℕ} (hi : i < (heights D).length)
    (hj : j < (heights D).length) (hij : i < j)
    (hyi : y ≤ rowOffset D i + (heights D)[i]) (hyj : rowOffset D j ≤ y) :
    j = i + 1 ∧ y = rowOffset D j := by
  have hs := band_separation D hi hij
  have hne : ¬i + 1 < j := by
    intro hh
    have := band_strict_separation D hi hj hh
    omega
  constructor <;> omega

end PushPuzzle.NCL

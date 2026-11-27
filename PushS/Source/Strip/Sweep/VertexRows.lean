/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.DrawingResources
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileBandwidth
import Mathlib.Algebra.Order.Group.Nat

import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition

/-!
# Actual word vertex indices and actual drawing rows

Each actual plane-word layer contains one vertex. Its actual compilation index is its layer
index, and its geometric row lies strictly between that layer's two actual row offsets.

## Main definitions

* `PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer`: the actual layer of an actual drawn vertex.

## Main results

* `PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer_val`: actual layer order equals actual vertex-list order.
* `PushPuzzle.NCL.Word.OrthogonalDrawing.vertex_rows_index`: actual rows lie in the corresponding actual layer.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

private theorem castBoundary_height {V E : Type*} {G : ConstraintGraph V E} {m n m' n' : ℕ}
    {top : Fin m → E} {bottom : Fin n → E} (P : GridDrawing.Open G top bottom)
    (hm : m' = m) (hn : n' = n) : (P.castBoundary hm hn).height = P.height := by
  cases hm
  cases hn
  rfl

/-- The actual geometric layer height is the actual layer layout's declared height. -/
theorem Slice.OrthogonalDrawing.geometric_height {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) : (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric L).height = L.layout.height := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hp, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  change ((GridDrawing.Cell.drawing v hp layout).castBoundary
    (GridDrawing.Pad.boundary_length left as right)
    (GridDrawing.Pad.boundary_length left bs right)).height = layout.height
  exact castBoundary_height _ _ _

/-- The actual drawn single-vertex layer has exactly one vertex in its actual flattened list. -/
theorem Slice.OrthogonalDrawing.vertexList_length {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) : (vertexList Prim.interp L.diagram).length = 1 := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hp, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  rfl

/-- The actual word layer containing each actual drawn diagram vertex. -/
@[expose] def Word.OrthogonalDrawing.vertexLayer {w : Word} {a b : List Color} :
    (D : w.OrthogonalDrawing a b) → D.diagram.Vtx Prim.interp → Fin w.length
  | .nil _ => fun v => v.elim
  | .cons layer rest =>
    show layer.diagram.Vtx Prim.interp ⊕ rest.diagram.Vtx Prim.interp → _ from
      Sum.elim (fun _ => ⟨0, by simp⟩) (fun v => (vertexLayer rest v).succ)

/-- Actual layer numbering agrees with the same diagram's actual vertex compilation index. -/
theorem Word.OrthogonalDrawing.vertexLayer_val {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (v : D.diagram.Vtx Prim.interp) :
    ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val = (vertexEquiv Prim.interp D.diagram v).val := by
  induction D with
  | nil _ => exact v.elim
  | cons layer rest ih =>
    cases v with
    | inl v =>
      have hi := (vertexEquiv Prim.interp layer.diagram v).isLt
      have hl := (PushPuzzle.NCL.Slice.OrthogonalDrawing.vertexList_length layer)
      change 0 = (vertexEquiv Prim.interp layer.diagram v).val
      omega
    | inr v =>
      change ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer rest) v).val + 1 =
        (vertexList Prim.interp layer.diagram).length +
          (vertexEquiv Prim.interp rest.diagram v).val
      rw [(PushPuzzle.NCL.Slice.OrthogonalDrawing.vertexList_length layer), ih]
      omega

private theorem rowOffset_cons {sl : Slice} {w : Word} {a b c : List Color}
    (layer : sl.OrthogonalDrawing a b) (rest : w.OrthogonalDrawing b c) (i : ℕ) :
    (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset (Word.OrthogonalDrawing.cons layer rest)) (i + 1) =
      layer.layout.height + (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset rest) i := by
  simp only [PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset, PushPuzzle.NCL.Word.OrthogonalDrawing.heights,
    List.take_succ_cons, List.sum_cons]

/-- Every actual drawn vertex lies strictly between its own actual layer's two row offsets. -/
theorem Word.OrthogonalDrawing.vertex_rows_index {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (v : D.diagram.Vtx Prim.interp) :
    (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val < ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v).2 ∧
      ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v).2 < (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) (((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val + 1) := by
  induction D with
  | nil _ => exact v.elim
  | cons layer rest ih =>
    cases v with
    | inl v =>
      have hr := (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric layer).vertex_rows v
      rw [(PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric_height layer)] at hr
      change 0 < ((PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric layer).vertex v).2 ∧
        ((PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric layer).vertex v).2 < (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset (Cslib.Complexity.NCL.Word.OrthogonalDrawing.cons layer rest)) (0 + 1)
      rw [rowOffset_cons]
      simpa only [rowOffset, List.take_zero, List.sum_nil, Nat.add_zero] using hr
    | inr v =>
      have hr := ih v
      change (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset (Cslib.Complexity.NCL.Word.OrthogonalDrawing.cons layer rest)) (((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer rest) v).val + 1) <
          ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric rest).vertex v).2 + (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric layer).height ∧
        ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric rest).vertex v).2 + (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric layer).height <
          (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset (Cslib.Complexity.NCL.Word.OrthogonalDrawing.cons layer rest)) ((((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer rest) v).val + 1) + 1)
      rw [rowOffset_cons, rowOffset_cons]
      rw [(PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric_height layer)]
      omega

private theorem row_interval_span {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {n bound i j yu yv : ℕ} (h : (PushPuzzle.NCL.Word.WidthBound w) a n)
    (hij : i ≤ j) (hspan : j - i ≤ bound)
    (hu : (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) i < yu ∧ yu < (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) (i + 1))
    (hv : (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) j < yv ∧ yv < (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) (j + 1)) :
    Nat.dist yu yv ≤ (bound + 1) * (4 * n + 6) := by
  have hm₀ : (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) i ≤ (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) j := List.monotone_sum_take (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D) hij
  have hm₁ : (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) (i + 1) ≤ (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset D) (j + 1) :=
    List.monotone_sum_take (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D) (by omega)
  have hk : j + 1 - i ≤ bound + 1 := by omega
  have he : i + (j + 1 - i) = j + 1 := by omega
  have ho := (PushPuzzle.NCL.Word.OrthogonalDrawing.rowOffset_add_le D) h i (j + 1 - i)
  rw [he] at ho
  have hp := Nat.mul_le_mul_right (4 * n + 6) hk
  simp only [Nat.dist]
  omega

/-- Actual vertex-index distance bounds the actual geometric row distance in the same drawing.
-/
theorem Word.OrthogonalDrawing.vertex_rows_span {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {n bound : ℕ} (h : (PushPuzzle.NCL.Word.WidthBound w) a n)
    (u v : D.diagram.Vtx Prim.interp)
    (hspan : Nat.dist (vertexEquiv Prim.interp D.diagram u).val
      (vertexEquiv Prim.interp D.diagram v).val ≤ bound) :
    Nat.dist ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex u).2 ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v).2 ≤
      (bound + 1) * (4 * n + 6) := by
  have hs : Nat.dist ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) u).val ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val ≤ bound := by
    rw [(PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer_val D) u, (PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer_val D) v]
    exact hspan
  have hu := (PushPuzzle.NCL.Word.OrthogonalDrawing.vertex_rows_index D) u
  have hv := (PushPuzzle.NCL.Word.OrthogonalDrawing.vertex_rows_index D) v
  rcases le_total ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) u).val ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val with hij | hji
  · apply row_interval_span D h hij (by simp only [Nat.dist] at hs; omega) hu hv
  · have hh := row_interval_span D (bound := bound) h hji
      (by simp only [Nat.dist] at hs; omega) hv hu
    simpa only [Nat.dist_comm] using hh

end PushPuzzle.NCL

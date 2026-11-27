/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.DrawingColumns
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition

import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad

/-!
# Canonical actual orthogonal drawings of bounded-width words

Retain each actual word layer, colored interfaces and exact vertex record. Replace its routing
by the existing deterministic `GridLayout.layer` algorithm. This constructs a drawing with fixed
column bounds for every point of every complete edge trace.

## Main definitions

* `PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical`: use the actual canonical layer-routing algorithm.
* `PushPuzzle.NCL.Word.OrthogonalDrawing.canonical`: apply that same routing throughout the actual word.

## Main results

* `PushPuzzle.NCL.Word.OrthogonalDrawing.canonical_columns_le`: all complete actual traces have bounded column.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Keep the exact layer and vertex, using the existing canonical routing algorithm. -/
@[expose] def Slice.OrthogonalDrawing.canonical {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) : sl.OrthogonalDrawing a b :=
  { L with layout := GridLayout.layer _ _ _ _ L.layout.arity }

/-- Use the canonical routing algorithm in every actual layer of the same checked word. -/
@[expose] def Word.OrthogonalDrawing.canonical {w : Word} {a b : List Color} :
    w.OrthogonalDrawing a b → w.OrthogonalDrawing a b
  | .nil a => .nil a
  | .cons layer rest => .cons (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical layer) (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical rest)

private theorem castBoundary_trace {V E : Type*} {G : ConstraintGraph V E} {m n m' n' : ℕ}
    {top : Fin m → E} {bottom : Fin n → E} (P : GridDrawing.Open G top bottom)
    (hm : m' = m) (hn : n' = n) (e : E) (p : GridRouting.Point) :
    (P.castBoundary hm hn).trace e p ↔ P.trace e p := by
  cases hm
  cases hn
  rfl

/-- Every actual canonical layer trace stays in the fixed column budget. -/
private theorem Slice.OrthogonalDrawing.canonical_columns_le {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) {n : ℕ} (ha : a.length ≤ n) (hb : b.length ≤ n)
    (e : (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L).diagram.Edge) (p : GridRouting.Point)
    (hp : (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical L)).trace e p) : p.1 ≤ Strip.Sweep.drawingWidth n := by
  rcases L with ⟨left, as, bs, right, v, hsl, hs, ht, hports, layout⟩
  have hs' := hs.trans (List.append_assoc left as right)
  have ht' := ht.trans (List.append_assoc left bs right)
  cases hs'
  cases ht'
  have hi : left.length + as.length + right.length ≤ n := by
    simpa only [List.length_append, Nat.add_assoc] using ha
  have ho : left.length + bs.length + right.length ≤ n := by
    simpa only [List.length_append, Nat.add_assoc] using hb
  change
    (((GridDrawing.Cell.drawing v hports (GridLayout.layer _ _ _ _ layout.arity)).castBoundary
      (GridDrawing.Pad.boundary_length left as right)
      (GridDrawing.Pad.boundary_length left bs right)).trace
        (GridDrawing.Pad.edgeEquiv left as bs right v e) p) at hp
  rw [castBoundary_trace] at hp
  exact PushPuzzle.NCL.GridLayout.layer_trace_column_le layout.arity hi ho hp

/-- Canonicalizing the actual checked drawing bounds every point on every complete edge trace.
-/
theorem Word.OrthogonalDrawing.canonical_columns_le {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) {n : ℕ} (h : (PushPuzzle.NCL.Word.WidthBound w) a n)
    (e : (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.Edge) (p : GridRouting.Point)
    (hp : (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).trace e p) : p.1 ≤ Strip.Sweep.drawingWidth n := by
  induction D generalizing p with
  | nil a =>
    cases e with
    | inl i =>
      have ha := h.start
      have hi := i.isLt
      change p.1 = 4 * i.val ∧ p.2 ≤ 1 at hp
      dsimp only [Strip.Sweep.drawingWidth]
      omega
    | inr e => exact e.elim
  | @cons sl w a b c layer rest ih =>
    have hl : Word.WellTyped [sl] a b := by
      rw [← layer.toWord_diagram]
      exact Diagram.wellTyped_toWord _ _
    have ha := h.start
    have hb : b.length ≤ n := h [sl] (List.prefix_append _ w) b hl
    have hr : PushPuzzle.NCL.Word.WidthBound w b n := h.of_append_right (u := [sl]) hl
    change GridDrawing.Comp.Trace (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical layer)) (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical rest)) e p at hp
    rcases hp with ⟨e', _, hp⟩ | ⟨_, e', _, hp⟩
    · exact (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical_columns_le layer) ha hb e' p hp
    · exact ih hr e' (p.1, p.2 - (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric (PushPuzzle.NCL.Slice.OrthogonalDrawing.canonical layer)).height) hp

/-- The same compiled word has a complete orthogonal graph drawing of uniformly bounded width.
-/
theorem Word.boundedOrthogonalDrawing_compile {w : Word} {n : ℕ}
    (hP : w.checkPlane = true) (hT : w.WellTyped [] []) (hW : (PushPuzzle.NCL.Word.WidthBound w) [] n) :
    ∃ P : GridDrawing.Closed w.compile.graph,
      ∀ e p, (P.path e).Contains p → p.1 ≤ Strip.Sweep.drawingWidth n := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  let Q := (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  have hQ : Q.diagram.toWord Prim.interp 0 = w := Q.toWord_diagram
  rw [← hQ, compile_toWord]
  refine ⟨(GridDrawing.Closed.finite Q.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close).ofFinite, ?_⟩
  intro e p hp
  have hf := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff
    (GridDrawing.Closed.finite Q.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close) _ _ _ e p).mp hp
  have hd := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close _ _ _ _ p).mp hf
  exact (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical_columns_le D) hW _ p ((PushPuzzle.NCL.GridDrawing.Open.close_path_mem (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q)) _ p hd)

end PushPuzzle.NCL

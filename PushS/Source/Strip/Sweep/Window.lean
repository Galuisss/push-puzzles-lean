/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.VertexRows
public import PushS.Source.Diagram.Word.DrawingCorrectness
public import PushS.Source.Strip.Sweep.CanonicalDrawing

/-!
# Complete-path windows in the actual canonical word drawing

Combine actual prefix width and actual vertex-list edge span in the same drawing. Actual layer
indices control actual vertex rows; every full path stays between its actual endpoint rows.
Finite numbering and native serialization retain the complete paths.

## Main definitions

* `Strip.Sweep.drawingSpan`: the resulting fixed longitudinal path-window length.

## Main results

* `PushPuzzle.NCL.Word.stripDrawing_compile`: the exact compiled graph has bounded full paths in fixed windows.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Longitudinal extent of the actual layers between endpoints of bounded compilation-index span.
-/
@[expose] def Strip.Sweep.drawingSpan (width bound : ℕ) : ℕ := (bound + 1) * (4 * width + 6)

private theorem index_span_of_compiled (D : Diagram Prim [] []) {bound : ℕ}
    (h : ∀ u v, ∀ p ∈ ((D.toWord Prim.interp 0).compile.graph u).ports,
      ∀ q ∈ ((D.toWord Prim.interp 0).compile.graph v).ports, p.1.edge = q.1.edge →
        Nat.dist u.val v.val ≤ bound)
    (u v : D.Vtx Prim.interp) {p q : WeightedPort D.Edge}
    (hp : p ∈ (D.graph Prim.interp u).ports) (hq : q ∈ (D.graph Prim.interp v).ports)
    (he : p.1.edge = q.1.edge) :
    Nat.dist (vertexEquiv Prim.interp D u).val (vertexEquiv Prim.interp D v).val ≤ bound := by
  have hp' : ⟨p.1.map (compileEdgeEquiv Prim.interp D), p.2⟩ ∈
      ((D.toWord Prim.interp 0).compile.graph (compileVertexEquiv Prim.interp D u)).ports := by
    rw [compile_graph_vertexEquiv]
    exact List.mem_map.mpr ⟨p, hp, rfl⟩
  have hq' : ⟨q.1.map (compileEdgeEquiv Prim.interp D), q.2⟩ ∈
      ((D.toWord Prim.interp 0).compile.graph (compileVertexEquiv Prim.interp D v)).ports := by
    rw [compile_graph_vertexEquiv]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  exact h _ _ _ hp' _ hq' (congrArg (compileEdgeEquiv Prim.interp D) he)

private theorem compiled_window_of_raw {w : Word} (D : w.OrthogonalDrawing [] [])
    {width span : ℕ}
    (hraw : ∀ e, ∃ start : ℕ, ∀ p, ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close.path e).Contains p →
      p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span) :
    ∀ e, ∃ start : ℕ, ∀ p, ((PushPuzzle.NCL.Word.DrawingData.compiled D).path e).Contains p →
      p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span := by
  have number (G : AndOrGraph) (h : G = AndOrGraph.ofFinite (finiteGraph Prim.interp D.diagram)) :
      let P : GridDrawing.Closed G.graph := h.symm ▸
        (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close).ofFinite
      ∀ e, ∃ start : ℕ, ∀ p, (P.path e).Contains p →
        p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span := by
    cases h
    dsimp only
    intro e
    obtain ⟨start, hs⟩ := hraw (D.diagram.numEquiv.symm e)
    refine ⟨start, fun p hp => ?_⟩
    have hf := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff
      (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close) _ _ _ e p).mp hp
    have hd := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close _ _ _ _ p).mp hf
    exact hs p hd
  have transport (u : Word) (h : D.diagram.toWord Prim.interp 0 = u) :
      let P : GridDrawing.Closed u.compile.graph := h ▸
        ((compile_toWord Prim.interp D.diagram).symm ▸
          (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close).ofFinite)
      ∀ e, ∃ start : ℕ, ∀ p, (P.path e).Contains p →
        p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span := by
    cases h
    exact number _ (compile_toWord Prim.interp D.diagram)
  exact transport w D.toWord_diagram

/-- This same actual canonical native drawing has complete paths in the stated fixed windows. -/
theorem Word.OrthogonalDrawing.compiled_strip_bounds {w : Word} {n bound : ℕ}
    (D : w.OrthogonalDrawing [] []) (hW : (PushPuzzle.NCL.Word.WidthBound w) [] n)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) :
    ∀ e, ∃ start : ℕ, ∀ p,
      ((PushPuzzle.NCL.Word.DrawingData.compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).path e).Contains p →
        p.1 ≤ Strip.Sweep.drawingWidth n ∧
        start ≤ p.2 ∧ p.2 ≤ start + Strip.Sweep.drawingSpan n bound := by
  let Q := (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  have hQ : Q.diagram.toWord Prim.interp 0 = w := Q.toWord_diagram
  have hIndexQ : ∀ u v, ∀ p ∈ ((Q.diagram.toWord Prim.interp 0).compile.graph u).ports,
      ∀ q ∈ ((Q.diagram.toWord Prim.interp 0).compile.graph v).ports,
        p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound := hQ.symm ▸ hIndex
  let P := (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close
  have hRaw (e : Q.diagram.Edge) : ∃ start : ℕ, ∀ p, (P.path e).Contains p →
      p.1 ≤ Strip.Sweep.drawingWidth n ∧ start ≤ p.2 ∧
        p.2 ≤ start + Strip.Sweep.drawingSpan n bound := by
    obtain ⟨wp, hp⟩ := P.source_port e
    obtain ⟨wq, hq⟩ := P.target_port e
    have hi := index_span_of_compiled Q.diagram hIndexQ (P.source e) (P.target e) hp hq rfl
    have hs := (PushPuzzle.NCL.Word.OrthogonalDrawing.vertex_rows_span Q) hW (P.source e) (P.target e) hi
    have he := P.edge_rows e
    change Nat.dist (P.vertex (P.source e)).2 (P.vertex (P.target e)).2 ≤ _ at hs
    refine ⟨(P.vertex (P.source e)).2, ?_⟩
    intro p hm
    have hc := (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical_columns_le D) hW e p ((PushPuzzle.NCL.GridDrawing.Open.close_path_mem (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q)) e p hm)
    have hy := (P.path e).row_bounds hm
    refine ⟨hc, hy.1, ?_⟩
    dsimp only [Strip.Sweep.drawingSpan]
    simp only [Nat.dist] at hs
    omega
  exact compiled_window_of_raw Q hRaw

/-- The same native graph has its exact original vertex array and complete fixed-window paths. -/
theorem Word.stripDrawing_compile_data {w : Word} {n bound : ℕ}
    (hP : w.checkPlane = true) (hT : w.WellTyped [] []) (hW : (PushPuzzle.NCL.Word.WidthBound w) [] n)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) :
    ∃ P : GridDrawing.Closed w.compile.graph,
      P.orthogonalDrawing.1 = PushPuzzle.NCL.Word.DrawingData.vertices w ∧ ∀ e, ∃ start : ℕ, ∀ p,
      (P.path e).Contains p → p.1 ≤ Strip.Sweep.drawingWidth n ∧
        start ≤ p.2 ∧ p.2 ≤ start + Strip.Sweep.drawingSpan n bound := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  exact ⟨PushPuzzle.NCL.Word.DrawingData.compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D), PushPuzzle.NCL.Word.DrawingData.compiled_vertices (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D),
    (PushPuzzle.NCL.Word.OrthogonalDrawing.compiled_strip_bounds D) hW hIndex⟩

/-- The same actual compiled graph has complete bounded-width paths in fixed longitudinal windows.
-/
theorem Word.stripDrawing_compile {w : Word} {n bound : ℕ}
    (hP : w.checkPlane = true) (hT : w.WellTyped [] []) (hW : (PushPuzzle.NCL.Word.WidthBound w) [] n)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) :
    ∃ P : GridDrawing.Closed w.compile.graph, ∀ e, ∃ start : ℕ, ∀ p,
      (P.path e).Contains p → p.1 ≤ Strip.Sweep.drawingWidth n ∧
        start ≤ p.2 ∧ p.2 ≤ start + Strip.Sweep.drawingSpan n bound := by
  obtain ⟨P, _, hp⟩ := PushPuzzle.NCL.Word.stripDrawing_compile_data hP hT hW hIndex
  exact ⟨P, hp⟩

end PushPuzzle.NCL

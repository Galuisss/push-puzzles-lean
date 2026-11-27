/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.TraceCorrectness
public import PushS.Source.Diagram.Word.DrawingCorrectness

/-!
# Native contacts of the actual canonical trace queries

The original creation-order native edge tags identify the same original canonical trace.
Its vertices and all pairwise contacts are the original compiled graph's actual incidences.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_native`: same native edge under exact original renaming.
* `PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_vertex`, `.trace_meet`: actual native trace contacts.
* `PushPuzzle.NCL.Word.DrawingData.TraceInput.compiled_trace`: complete original paths lie in the emitted mask.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib Diagram

/-- The exact original native edge tag queries precisely its original canonical diagram trace. -/
theorem TraceInput.trace_native {width : ℕ} {w : Word} (D : w.OrthogonalDrawing [] [])
    (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width) (e : Fin w.compile.edgeCount) (p : GridRouting.Point) :
    (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val p.1 p.2).trace width = true ↔
      (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).trace ((nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm e) p := by
  have hn : (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.num ((nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm e) = e.val :=
    (nativeEdgeEquiv_val (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) _).symm.trans
      (congrArg Fin.val ((nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).apply_symm_apply e))
  rw [PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_eq D hwidth]
  constructor
  · rintro ⟨f, hf, hp⟩
    have he : f = (nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm e :=
      (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D).diagram.num_injective (hf.trans hn.symm)
    exact he ▸ hp
  · intro hp
    exact ⟨_, hn, hp⟩

private theorem native_incident {w : Word} (D : w.OrthogonalDrawing [] [])
    (v : D.diagram.Vtx Prim.interp) (e : D.diagram.Edge)
    (h : GridDrawing.Incident (D.diagram.graph Prim.interp) v e) :
    GridDrawing.Incident w.compile.graph (nativeVertexEquiv D v) (nativeEdgeEquiv D e) := by
  obtain ⟨dir, hd⟩ := h
  exact ⟨dir, (native_hasPort_iff D v e dir).mpr hd⟩

/-- A native canonical trace touches only the actual original incident native vertices. -/
theorem TraceInput.trace_vertex {width : ℕ} {w : Word} (D : w.OrthogonalDrawing [] [])
    (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width) (e : Fin w.compile.edgeCount)
    (v : Fin w.compile.vertices.length)
    (h : (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex v).1
      ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex v).2).trace width = true) :
    GridDrawing.Incident w.compile.graph v e := by
  have ht := (PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_native D hwidth e _).mp h
  let rawv := (nativeVertexEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm v
  have hv : (compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex v = (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex rawv := by
    simpa only [rawv, Equiv.apply_symm_apply] using compiled_vertex (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) rawv
  rw [hv] at ht
  have hi := (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex_meet _ rawv ht
  simpa only [rawv, Equiv.apply_symm_apply] using native_incident (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) rawv _ hi

/-- Different original native canonical traces meet only at an actual common incident vertex. -/
theorem TraceInput.trace_meet {width : ℕ} {w : Word} (D : w.OrthogonalDrawing [] [])
    (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width) (e f : Fin w.compile.edgeCount) (p : GridRouting.Point)
    (hef : e ≠ f) (he : (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val p.1 p.2).trace width = true)
    (hf : (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w f.val p.1 p.2).trace width = true) :
    ∃ v, p = (compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).vertex v ∧
      GridDrawing.Incident w.compile.graph v e ∧ GridDrawing.Incident w.compile.graph v f := by
  have he' := (PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_native D hwidth e p).mp he
  have hf' := (PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_native D hwidth f p).mp hf
  have hne : (nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm e ≠ (nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm f :=
    (nativeEdgeEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).symm.injective.ne hef
  obtain ⟨v, hp, hv, hw⟩ := (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).meet _ _ p hne he' hf'
  refine ⟨nativeVertexEquiv (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) v, hp.trans (compiled_vertex (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) v).symm, ?_, ?_⟩
  · simpa only [Equiv.apply_symm_apply] using native_incident (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) v _ hv
  · simpa only [Equiv.apply_symm_apply] using native_incident (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D) v _ hw

/-- Every point of the original full compiled path is accepted by the same native trace query. -/
theorem TraceInput.compiled_trace {width : ℕ} {w : Word} (D : w.OrthogonalDrawing [] [])
    (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width) (e : Fin w.compile.edgeCount) (p : GridRouting.Point)
    (hp : ((compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)).path e).Contains p) :
    (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val p.1 p.2).trace width = true := by
  let Q := (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  have number (g : AndOrGraph) (h : g = AndOrGraph.ofFinite (finiteGraph Prim.interp Q.diagram)) :
      let P : GridDrawing.Closed g.graph := h.symm ▸
        (GridDrawing.Closed.finite Q.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close).ofFinite
      ∀ e p, (P.path e).Contains p → (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk w e.val p.1 p.2).trace width = true := by
    cases h
    dsimp only
    intro e p hp
    have hf := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff
      (GridDrawing.Closed.finite Q.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close) _ _ _ e p).mp hp
    have hd := (PushPuzzle.NCL.GridDrawing.Closed.reindex_path_contains_iff (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close _ _ _ _ p).mp hf
    exact (PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_eq D hwidth e.val p.1 p.2).mpr
      ⟨Q.diagram.numEquiv.symm e, Q.diagram.num_numEquiv_symm e,
        (PushPuzzle.NCL.GridDrawing.Open.close_path_mem (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q)) _ p hd⟩
  have transport (u : Word) (h : Q.diagram.toWord Prim.interp 0 = u) :
      let P : GridDrawing.Closed u.compile.graph := h ▸
        ((compile_toWord Prim.interp Q.diagram).symm ▸
          (GridDrawing.Closed.finite Q.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric Q).close).ofFinite)
      ∀ e p, (P.path e).Contains p → (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk u e.val p.1 p.2).trace width = true := by
    cases h
    dsimp only
    intro e p hp
    have ht := number _ (compile_toWord Prim.interp Q.diagram) e p hp
    exact (congrArg (fun u => (PushPuzzle.NCL.Word.DrawingData.TraceInput.mk u e.val p.1 p.2).trace width)
      Q.toWord_diagram).trans ht
  exact transport w Q.toWord_diagram e p hp

end PushPuzzle.NCL.Word.DrawingData

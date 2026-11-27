/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.EdgePath

/-!
# Continuous planar correctness of the emitted native drawing arrays

The emitted native routes reconstruct actual downward grid paths. Original canonical trace
queries certify all their lattice contacts, retaining the actual original vertex separation and
native graph incidences. The resulting closed drawing gives the standard continuous planar
certificate for these exact emitted arrays.

## Main definitions

* `PushPuzzle.NCL.Word.DrawingData.selected`: actual native drawing with the emitted selected edge paths.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.selected_drawing`: exact standard vertex and route arrays.
* `PushPuzzle.NCL.Word.DrawingData.selected_window`: complete paths in fixed longitudinal windows.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib

/-- Actual closed native drawing whose paths are the emitted fixed-window route selections. -/
noncomputable def selected {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) : GridDrawing.Closed w.compile.graph :=
  let P := compiled (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  { vertex := P.vertex
    vertex_injective := P.vertex_injective
    vertex_separation := P.vertex_separation
    source := P.source
    target := P.target
    source_port := P.source_port
    target_port := P.target_port
    edge_rows := P.edge_rows
    path := PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath D hg hwidth hIndex
    source_eq := P.source_eq
    target_eq := P.target_eq
    vertex_meet := fun e v hp => PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_vertex D hwidth e v
      (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_points D hg hwidth hIndex e _ hp)
    meet := fun e f p hne he hf => PushPuzzle.NCL.Word.DrawingData.TraceInput.trace_meet D hwidth e f p hne
      (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_points D hg hwidth hIndex e p he)
      (PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_points D hg hwidth hIndex f p hf) }

/-- The actual selected closed drawing serializes to exactly the emitted standard native arrays. -/
theorem selected_drawing {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) :
    (selected D hg hwidth hIndex).orthogonalDrawing =
      drawing width (Strip.Sweep.drawingSpan width bound) w := by
  apply Prod.ext
  · exact compiled_vertices (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)
  · apply List.ext_getElem
    · simp only [GridDrawing.Closed.orthogonalDrawing, routes, drawing,
        List.length_ofFn, List.length_map, List.length_range, Word.compile]
    · intro i hi hj
      simp only [GridDrawing.Closed.orthogonalDrawing, List.length_ofFn] at hi
      simp only [GridDrawing.Closed.orthogonalDrawing, drawing, routes, List.getElem_ofFn,
        List.getElem_map, List.getElem_range]
      exact PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_unitRoute D hg hwidth hIndex ⟨i, hi⟩

/-- Every complete emitted native path lies in its fixed source-row rectangle. -/
theorem selected_window {width bound : ℕ} {w : Word}
    (D : w.OrthogonalDrawing [] []) (hg : w.compile.Bounded) (hwidth : (PushPuzzle.NCL.Word.WidthBound w) [] width)
    (hIndex : ∀ u v, ∀ p ∈ (w.compile.graph u).ports, ∀ q ∈ (w.compile.graph v).ports,
      p.1.edge = q.1.edge → Nat.dist u.val v.val ≤ bound) :
    ∀ e, ∃ start : ℕ, ∀ p, ((selected D hg hwidth hIndex).path e).Contains p →
      p.1 ≤ Strip.Sweep.drawingWidth width ∧ start ≤ p.2 ∧
        p.2 ≤ start + Strip.Sweep.drawingSpan width bound := by
  intro e
  exact ⟨((PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position false).2,
    PushPuzzle.NCL.Word.DrawingData.EdgeInput.selectedPath_window D hg hwidth hIndex e⟩

end PushPuzzle.NCL.Word.DrawingData

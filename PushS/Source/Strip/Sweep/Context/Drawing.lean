/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Resources
public import PushS.Source.Strip.Sweep.CanonicalDrawing
public import PushS.Source.Strip.Sweep.Context.Stages
public import PushS.Source.Strip.Sweep.Window
public import PushS.Source.Strip.Sweep.ContinuousWindow
public import PushS.Source.Strip.Sweep.SegmentDensity

/-!
# Actual bounded-width drawings of the emitted native strip graph

The actual emitted program has bounded prefix stacks. Canonicalizing the existing exact word
drawing gives bounded columns for all complete traces, and the same finite compiled graph
inherits the same complete-path bound.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.program_layered_drawing`: actual word layers with bounded full traces.
* `PushPuzzle.NCL.Strip.Sweep.Context.program_drawing`: the same native graph has bounded complete edge paths.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- The same actual program has canonical complete traces and bounded actual layer heights. -/
theorem program_layered_drawing :
    ∃ D : C.program.OrthogonalDrawing [] [],
      (∀ e p, (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).trace e p → p.1 ≤ drawingWidth (widthBudget K)) ∧
        ∀ h ∈ (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D), h ≤ 4 * widthBudget K + 6 := by
  obtain ⟨D⟩ := Word.orthogonalDrawing C.program_checkPlane C.program_wellTyped
  exact ⟨(PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D), (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical_columns_le D) C.program_widthBound,
    (PushPuzzle.NCL.Word.OrthogonalDrawing.heights_le (PushPuzzle.NCL.Word.OrthogonalDrawing.canonical D)) C.program_widthBound⟩

/-- Every complete edge path of an actual drawing of the same native output has constant width.
-/
theorem program_drawing :
    ∃ P : GridDrawing.Closed C.program.compile.graph,
      ∀ e p, (P.path e).Contains p → p.1 ≤ drawingWidth (widthBudget K) :=
  PushPuzzle.NCL.Word.boundedOrthogonalDrawing_compile C.program_checkPlane C.program_wellTyped
    C.program_widthBound

/-- The same native output has its exact original vertex array, simple fixed-window routes,
and the stated actual vertex and normalized-route feature counts in every strip panel. -/
theorem program_panel_drawing_data :
    ∃ P : GridDrawing.Closed C.program.compile.graph,
      P.orthogonalDrawing.1 = PushPuzzle.NCL.Word.DrawingData.vertices C.program ∧
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing P.incidenceGraph P.orthogonalDrawing ∧
      (∀ e, ∃ start : ℕ, ∀ q : ℝ × ℝ, q ∈ Cslib.Orthogonal.support (P.path e).unitRoute →
        0 ≤ q.1 ∧ q.1 ≤ drawingWidth (widthBudget K) ∧ (start : ℝ) ≤ q.2 ∧
          q.2 ≤ (start : ℝ) +
            drawingSpan (widthBudget K) ((height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1)) ∧
      (∀ panel, Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1) ∧
      (∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelVisit P panel) ≤
        6 * (drawingWidth (widthBudget K) + 1)) ∧
      ∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelSegment P panel) ≤
        12 * (drawingWidth (widthBudget K) + 1) := by
  obtain ⟨P, hv, hp⟩ := PushPuzzle.NCL.Word.stripDrawing_compile_data C.program_checkPlane
    C.program_wellTyped C.program_widthBound C.program_vertex_index_bounds
  have hW : ∀ e p, (P.path e).Contains p → p.1 ≤ drawingWidth (widthBudget K) := by
    intro e p he
    obtain ⟨_, hs⟩ := hp e
    exact (hs p he).1
  have hd (v) : (C.program.compile.graph v).ports.length ≤ 3 :=
    (C.program_valid.isAndOr v).shape.1.le
  exact ⟨P, hv, P.isPlanarOrthogonalDrawing, (PushPuzzle.NCL.GridDrawing.Closed.unitRoute_window P) hp, (PushPuzzle.NCL.GridDrawing.Closed.panel_vertices_le P),
    (fun panel => (PushPuzzle.NCL.GridDrawing.Closed.panel_visits_le P) hd _ panel hW),
    fun panel => (PushPuzzle.NCL.GridDrawing.Closed.panel_segments_le P) hd _ panel hW⟩

end PushPuzzle.NCL.Strip.Sweep.Context

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Program
public import PushS.Source.Diagram.Word.DrawingCorrectness
public import PushS.Source.Diagram.Word.SelectedDrawing

/-!
# Actual canonical vertex coordinates of the word-network strip

Serialize the original word's exact canonical vertex centers using its actual original prefix
compiler states. The same vertex array occurs in an actual complete drawing of the same native
graph, with the already established fixed windows and strip-panel feature bounds.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.Sweep.vertexPositions`: actual canonical native vertex coordinates.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_vertexPositions`: standard coordinate emission.
* `PushPuzzle.NCL.HWord.Strip.Sweep.panel_drawing_data`: the same array and native graph have the strip bounds.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib _root_.Turing.MultiTapeTM

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The original native word's actual canonical vertex centers in its original vertex order. -/
@[expose] def vertexPositions (n : ℕ) : Orthogonal.Route :=
  PushPuzzle.NCL.Word.DrawingData.vertices (program (n := n) H hq)

/-- The same actual native vertex coordinates emit in standard binary encoded polynomial time.
-/
theorem computableInPolyTime_vertexPositions :
    ComputableInPolyTime (vertexPositions H hq) encUnary Orthogonal.encRoute :=
  PushPuzzle.NCL.Word.DrawingData.computableInPolyTime_vertices.comp (computableInPolyTime_program H hq)

/-- Fixed horizontal extent of the actual native strip for this alphabet. -/
@[expose] def drawingWidth (q : ℕ) : ℕ :=
  PushPuzzle.NCL.Strip.Sweep.drawingWidth (PushPuzzle.NCL.Strip.Sweep.widthBudget (edgeBudget q))

/-- Fixed complete-route longitudinal extent of the actual native strip for this alphabet. -/
@[expose] def drawingSpan (q : ℕ) : ℕ :=
  PushPuzzle.NCL.Strip.Sweep.drawingSpan (PushPuzzle.NCL.Strip.Sweep.widthBudget (edgeBudget q))
    ((PushPuzzle.NCL.Strip.Sweep.height (edgeBudget q) + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1)

/-- The same actual native graph's standard vertex and directed edge-route arrays. -/
@[expose] def drawing (n : ℕ) : Graph.OrthogonalDrawing :=
  PushPuzzle.NCL.Word.DrawingData.drawing (PushPuzzle.NCL.Strip.Sweep.widthBudget (edgeBudget q)) (drawingSpan q)
    (program (n := n) H hq)

/-- The complete same actual native drawing emits in standard polynomial time. -/
theorem computableInPolyTime_drawing :
    ComputableInPolyTime (drawing H hq) encUnary Graph.encOrthogonalDrawing :=
  (PushPuzzle.NCL.Word.DrawingData.computableInPolyTime_drawing
    (PushPuzzle.NCL.Strip.Sweep.widthBudget (edgeBudget q)) (drawingSpan q)).comp
      (computableInPolyTime_program H hq)

/-- These exact emitted arrays describe the actual native graph, with fixed complete-route
windows and the actual panel vertex, visit, and segment budgets. -/
theorem emitted_panel_drawing :
    ∃ P : GridDrawing.Closed (program (n := n) H hq).compile.graph,
      P.orthogonalDrawing = drawing H hq n ∧
      Graph.IsPlanarOrthogonalDrawing P.incidenceGraph (drawing H hq n) ∧
      (∀ e, ∃ start : ℕ, ∀ p : ℝ × ℝ, p ∈ Orthogonal.support (P.path e).unitRoute →
        0 ≤ p.1 ∧ p.1 ≤ drawingWidth q ∧
          (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + drawingSpan q) ∧
      (∀ panel, Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1) ∧
      (∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelVisit P panel) ≤ 6 * (drawingWidth q + 1)) ∧
      ∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelSegment P panel) ≤ 12 * (drawingWidth q + 1) := by
  let C := context (n := n) H hq
  obtain ⟨D⟩ := Word.orthogonalDrawing C.program_checkPlane C.program_wellTyped
  let P := PushPuzzle.NCL.Word.DrawingData.selected D C.program_valid.1
    C.program_widthBound C.program_vertex_index_bounds
  have he : P.orthogonalDrawing = drawing H hq n :=
    PushPuzzle.NCL.Word.DrawingData.selected_drawing D C.program_valid.1
      C.program_widthBound C.program_vertex_index_bounds
  have hp := PushPuzzle.NCL.Word.DrawingData.selected_window D C.program_valid.1
    C.program_widthBound C.program_vertex_index_bounds
  have hW : ∀ e p, (P.path e).Contains p → p.1 ≤ drawingWidth q := by
    intro e p he
    obtain ⟨_, hs⟩ := hp e
    exact (hs p he).1
  have hd (v) : (C.program.compile.graph v).ports.length ≤ 3 :=
    (C.program_valid.isAndOr v).shape.1.le
  exact ⟨P, he, he ▸ P.isPlanarOrthogonalDrawing, (PushPuzzle.NCL.GridDrawing.Closed.unitRoute_window P) hp, (PushPuzzle.NCL.GridDrawing.Closed.panel_vertices_le P),
    (fun panel => (PushPuzzle.NCL.GridDrawing.Closed.panel_visits_le P) hd _ panel hW), fun panel => (PushPuzzle.NCL.GridDrawing.Closed.panel_segments_le P) hd _ panel hW⟩

/-- The actual original native graph has these same emitted vertex positions and full strip
geometry, including all continuous route windows and actual per-panel feature bounds. -/
theorem panel_drawing_data :
    let K := edgeBudget q
    let width := PushPuzzle.NCL.Strip.Sweep.drawingWidth (PushPuzzle.NCL.Strip.Sweep.widthBudget K)
    let span := PushPuzzle.NCL.Strip.Sweep.drawingSpan (PushPuzzle.NCL.Strip.Sweep.widthBudget K)
      ((PushPuzzle.NCL.Strip.Sweep.height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1)
    ∃ P : GridDrawing.Closed (program (n := n) H hq).compile.graph,
      P.orthogonalDrawing.1 = vertexPositions H hq n ∧
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing P.incidenceGraph P.orthogonalDrawing ∧
      (∀ e, ∃ start : ℕ, ∀ p : ℝ × ℝ, p ∈ Orthogonal.support (P.path e).unitRoute →
        0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span) ∧
      (∀ panel, Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1) ∧
      (∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelVisit P panel) ≤ 6 * (width + 1)) ∧
      ∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelSegment P panel) ≤ 12 * (width + 1) :=
  (context H hq).program_panel_drawing_data

end PushPuzzle.NCL.HWord.Strip.Sweep

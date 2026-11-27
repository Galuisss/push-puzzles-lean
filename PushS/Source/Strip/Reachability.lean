/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Native
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal
public import PushS.Source.Strip.Sweep.SegmentDensity
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Encoding

/-!
# Constraint-logic reachability with a fixed strip drawing

Inputs contain the standard native AND/OR graph, its two direction vectors, and standard integer
vertex and route arrays. A fixed horizontal width and fixed whole-route longitudinal span bound
the complete continuous supports. Every unit-height panel has the stated vertex, route-visit,
and route-segment bounds.

## Main definitions

* `PushPuzzle.NCL.StripAndOrNCL.Instance`: standard native graph, configurations, and drawing arrays.
* `PushPuzzle.NCL.StripAndOrNCL.ValidDrawing`: complete strip geometry of those actual arrays.
* `StripAndOrNCL`: configuration reachability with the fixed drawing bounds.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

/-- A native AND/OR reachability instance and its standard integer drawing arrays. -/
structure StripAndOrNCL.Instance where
  /-- The standard native graph and its two complete direction vectors. -/
  ncl : AndOrNCL.Instance
  /-- Vertex positions and edge routes in the same original native orders. -/
  drawing : Graph.OrthogonalDrawing

/-- Standard framed native reachability and standard binary-coordinate drawing arrays. -/
enc_structure encStripAndOrNCL : PushPuzzle.NCL.StripAndOrNCL.Instance where
  ncl : encAndOrNCL, drawing : Graph.encOrthogonalDrawing

/-- The actual native drawing has fixed complete-route windows and fixed panel feature budgets.
-/
@[expose] def StripAndOrNCL.ValidDrawing (width span : ℕ) (x : PushPuzzle.NCL.StripAndOrNCL.Instance) : Prop :=
  ∃ P : GridDrawing.Closed x.ncl.graph.graph,
    P.orthogonalDrawing = x.drawing ∧
    Graph.IsPlanarOrthogonalDrawing P.incidenceGraph x.drawing ∧
    (∀ e, ∃ start : ℕ, ∀ p : ℝ × ℝ, p ∈ Orthogonal.support (P.path e).unitRoute →
      0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span) ∧
    (∀ panel, Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1) ∧
    (∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelVisit P panel) ≤ 6 * (width + 1)) ∧
    ∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelSegment P panel) ≤ 12 * (width + 1)

/-- Native configuration reachability with an actual drawing of fixed width and complete span.
-/
@[expose] def StripAndOrNCL (width span : ℕ) : Set PushPuzzle.NCL.StripAndOrNCL.Instance :=
  {x | x.ncl ∈ AndOrNCL ∧ x.ncl.graph.graph.LoopFree ∧ PushPuzzle.NCL.StripAndOrNCL.ValidDrawing width span x}

end PushPuzzle.NCL

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute

/-! Exact unit subdivision used inside the strip compiler. -/

public section
namespace PushPuzzle.NCL.GridDrawing

open Cslib.Complexity.NCL

/-- Unit-grid adjacency used by the strip path traversal. -/
def unitGraph : SimpleGraph Cslib.Orthogonal.Point := Cslib.Complexity.NCL.GridDrawing.unitGraph

end PushPuzzle.NCL.GridDrawing

namespace PushPuzzle.NCL.GridRouting.Path

open Cslib.Complexity.NCL Cslib.Complexity.NCL.GridRouting

/-- The complete unit traversal of a native monotone grid path. -/
def unitWalk {p q : Point} (P : Path p q) :
    PushPuzzle.NCL.GridDrawing.unitGraph.Walk (GridDrawing.integerPoint p) (GridDrawing.integerPoint q) :=
  Cslib.Complexity.NCL.GridRouting.Path.unitWalk P

theorem unitWalk_horizontal_support (x x' y : ℕ) :
    (unitWalk (.horizontal x x' y)).support =
      Cslib.Orthogonal.segmentWalk (GridDrawing.integerPoint (x, y)) (GridDrawing.integerPoint (x', y)) :=
  Cslib.Complexity.NCL.GridDrawing.support_segmentUnitWalk
    (GridDrawing.integerPoint (x, y)) (GridDrawing.integerPoint (x', y)) (.inr rfl)

theorem unitWalk_vertical_support (x y y' : ℕ) (h : y ≤ y') :
    (unitWalk (.vertical x y y' h)).support =
      Cslib.Orthogonal.segmentWalk (GridDrawing.integerPoint (x, y)) (GridDrawing.integerPoint (x, y')) :=
  Cslib.Complexity.NCL.GridDrawing.support_segmentUnitWalk
    (GridDrawing.integerPoint (x, y)) (GridDrawing.integerPoint (x, y')) (.inl rfl)

theorem unitWalk_comp_support {p q r : Point} (P : Path p q) (Q : Path q r) :
    (unitWalk (.comp P Q)).support = (unitWalk P).support ++ (unitWalk Q).support.tail :=
  SimpleGraph.Walk.support_append _ _

/-- Every visited lattice point belongs to the original native path. -/
theorem unitWalk_trace {p q : Point} (P : Path p q) (u : Cslib.Orthogonal.Point)
    (hu : u ∈ (unitWalk P).support) : ∃ x, GridDrawing.integerPoint x = u ∧ P.Contains x :=
  Cslib.Complexity.NCL.GridRouting.Path.unitWalk_trace P u hu

theorem unitRoute_sublist_unitWalk {p q : Point} (P : Path p q) :
    P.unitRoute.Sublist (unitWalk P).support := by
  change (unitWalk P).bypass.support.Sublist (unitWalk P).support
  exact (unitWalk P).support_bypass_sublist_support

/-- A subdivision with distinct listed points already equals its normalized route. -/
theorem unitRoute_eq_unitWalk {p q : Point} (P : Path p q)
    (h : (unitWalk P).support.Nodup) : P.unitRoute = (unitWalk P).support := by
  have hp : (unitWalk P).IsPath := by
    rw [SimpleGraph.Walk.isPath_def]
    exact h
  change (unitWalk P).bypass.support = (unitWalk P).support
  rw [hp.bypass_eq_self]

end PushPuzzle.NCL.GridRouting.Path

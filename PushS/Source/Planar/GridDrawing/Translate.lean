/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Planar.GridDrawing.UnitRoute
import all PushS.Source.Planar.GridDrawing.UnitRoute
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute
public import CslibFrontier.Foundations.Geometry.Orthogonal.Macrocell

/-!
# Exact unit subdivision under grid translation

Translate the actual original grid path by nonnegative integer coordinates. Segment subdivision
and path concatenation retain exactly the translated original unit-walk point list.

## Main results

* `PushPuzzle.NCL.GridRouting.Path.unitWalk_translate`: exact original unit-subdivision translation.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib

private theorem walk_translate (a d t : Orthogonal.Point) (n : ℕ) :
    Orthogonal.walk (a + t) d n = Orthogonal.translate t (Orthogonal.walk a d n) := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [Orthogonal.walk, Orthogonal.translate, List.map_cons]
    congr 1
    have he : a + t + d = a + d + t := by abel
    rw [he, ih]
    rfl

private theorem segmentWalk_translate (a b t : Orthogonal.Point) :
    Orthogonal.segmentWalk (a + t) (b + t) =
      Orthogonal.translate t (Orthogonal.segmentWalk a b) := by
  have hd : Orthogonal.direction (a + t) (b + t) = Orthogonal.direction a b := by
    simp only [Orthogonal.direction, Prod.fst_add, Prod.snd_add, add_lt_add_iff_right]
  have hl : Orthogonal.length (a + t) (b + t) = Orthogonal.length a b := by
    simp only [Orthogonal.length, Prod.fst_add, Prod.snd_add, add_sub_add_right_eq_sub]
  rw [Orthogonal.segmentWalk, hd, hl, walk_translate]
  rfl

namespace GridRouting.Path

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridRouting Cslib.Complexity.NCL.GridRouting.Path

/-- Translating a path retains exactly its translated original unit-subdivision point list. -/
theorem unitWalk_translate {p q : GridRouting.Point} (P : Path p q) (dx dy : ℕ) :
    (PushPuzzle.NCL.GridRouting.Path.unitWalk (P.translate dx dy)).support =
      Orthogonal.translate (dx, dy) (PushPuzzle.NCL.GridRouting.Path.unitWalk P).support := by
  induction P with
  | horizontal x x' y =>
    rw [translate, unitWalk_horizontal_support, unitWalk_horizontal_support]
    simpa only [GridDrawing.integerPoint, Prod.mk_add_mk, Nat.cast_add] using
      segmentWalk_translate (GridDrawing.integerPoint (x, y))
        (GridDrawing.integerPoint (x', y)) (dx, dy)
  | vertical x y y' h =>
    rw [translate, unitWalk_vertical_support, unitWalk_vertical_support]
    simpa only [GridDrawing.integerPoint, Prod.mk_add_mk, Nat.cast_add] using
      segmentWalk_translate (GridDrawing.integerPoint (x, y))
        (GridDrawing.integerPoint (x, y')) (dx, dy)
  | comp P Q ihP ihQ =>
    rw [translate, unitWalk_comp_support, unitWalk_comp_support, ihP, ihQ]
    simp only [Orthogonal.translate, List.map_append, List.map_tail]

end GridRouting.Path
end PushPuzzle.NCL

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPolyTimeEmissionCorrect
public import PushS.Boundary

/-! Computing the actual strict-interior target inventory from its emitted segments. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS Turing.MultiTapeTM

/-- The actual strict-interior test on the target's unary rectangle. -/
@[expose] def interiorPoint (source : PointSource) (point : ℕ × ℕ) : Bool :=
  decide (0 < point.1 ∧ point.1 + 1 < source.width ∧
    0 < point.2 ∧ point.2 + 1 < source.height)

/-- Count the actual represented target holes away from the four boundary edges. -/
@[expose] def interiorCount (source : PointSource) : ℕ :=
  ((holePoints source).filter (interiorPoint source)).length

/-- The unary point predicate tests precisely absence from the genuine outer frame. -/
theorem interiorPoint_cell (source : PointSource) (q : Cell source.width source.height) :
    interiorPoint source (cellPoint source.width source.height q) = true ↔ q ∉ Boundary.frame := by
  change interiorPoint source (q.1.val, q.2.val) = true ↔ _
  simp only [interiorPoint, decide_eq_true_eq,
    Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
    Finset.mem_univ, true_and]
  have hx := q.1.isLt
  have hy := q.2.isLt
  omega

/-- The machine counts exactly the actual finite target bitmap minus its outer frame. -/
theorem interiorCount_correct (source : PointSource) :
    interiorCount source =
      (SegmentRecipe.holes source.width source.height source.segments \ Boundary.frame).card := by
  unfold interiorCount
  rw [point_filter_count _ _ (holePoints_nodup source) (holePoints_finset source)]
  apply congrArg Finset.card
  ext q
  simp only [Finset.mem_filter, Finset.mem_sdiff, interiorPoint_cell]

/-- The strict-interior predicate is computed by a standard unary machine on all raw inputs. -/
@[fun_prop] theorem interiorPoint_polyTime :
    ComputableInPolyTime (fun p : PointSource × (ℕ × ℕ) => interiorPoint p.1 p.2)
      (encPair encPointSource Bitmap.encPoint) encBool := by
  unfold interiorPoint Bitmap.encPoint
  fun_prop

/-- The actual target interior inventory emits in standard polynomial time from the segment source. -/
@[fun_prop] theorem interiorCount_polyTime :
    ComputableInPolyTime interiorCount encPointSource encUnary := by
  have hf := ComputableInPolyTime.filterWithInput
    (test := interiorPoint) holePoints_polyTime interiorPoint_polyTime
  unfold interiorCount
  fun_prop

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTreeDirections
import all PushS.CombTreeDirections
import all PushS.PreparedRayOrder

/-! The genuine two sides of every actual source/tooth crossing occupy their exact clockwise octants. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem left_ray_direction {z : ℂ} (hx : z.re < 0) (hshape : z.im = 0 ∨ z.im = z.re) :
    (z.arg : Real.Angle) = octantAngle 3 ∨ (z.arg : Real.Angle) = octantAngle 4 := by
  rcases hshape with hy | hy
  · right
    rw [Complex.arg_eq_pi_iff.mpr ⟨hx, hy⟩]
    exact octant_left.symm
  · left
    have hpoint : z = ((-z.re : ℝ) : ℂ) * (-1 - Complex.I) := by
      apply Complex.ext
      · simp
      · rw [hy]
        simp
    have harg : z.arg = -(3 * Real.pi / 4) := by
      rw [hpoint]
      simpa only [Complex.ofReal_neg] using
        (Complex.arg_real_mul (-1 - Complex.I) (neg_pos.mpr hx)).trans arg_negative_diagonal
    rw [harg]
    change ((-(3 * Real.pi / 4) : ℝ) : Real.Angle) = ((-(3 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)
    congr 1
    ring

private theorem right_ray_direction {z : ℂ} (hx : 0 < z.re) (hshape : z.im = 0 ∨ z.im = z.re) :
    (z.arg : Real.Angle) = octantAngle 0 ∨ (z.arg : Real.Angle) = octantAngle 7 := by
  rcases hshape with hy | hy
  · left
    rw [Complex.arg_eq_zero_iff.mpr ⟨hx.le, hy⟩]
    exact octant_right.symm
  · right
    have hpoint : z = (z.re : ℂ) * (1 + Complex.I) := by
      apply Complex.ext
      · simp
      · rw [hy]
        simp
    have harg : z.arg = Real.pi / 4 := by
      rw [hpoint]
      exact (Complex.arg_real_mul (1 + Complex.I) hx).trans arg_diagonal
    rw [harg]
    change ((Real.pi / 4 : ℝ) : Real.Angle) = ((-(7 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle)
    rw [show (-(7 : ℝ) * Real.pi / 4) = Real.pi / 4 - 2 * Real.pi by ring]
    simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]

/-- Actual ascending-side source rays point southwest or west, and return-side rays point east or northeast. -/
theorem edgeFragment_crossing_direction (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    if (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) then
      ((((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).arg : Real.Angle) = octantAngle 0 ∨
        (((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).arg : Real.Angle) = octantAngle 7)
    else
      ((((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).arg : Real.Angle) = octantAngle 3 ∨
        (((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).arg : Real.Angle) = octantAngle 4) := by
  have hshape := edgeFragment_crossing_shape width height hd hfit edge hhead hit side
  cases hreturn : (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    exact left_ray_direction ((edgeFragment_crossing_re_neg width height hd hfit edge hhead hit side).mpr hreturn) hshape
  | true =>
    simp only [ite_true]
    exact right_ray_direction ((edgeFragment_crossing_re_pos width height hd hfit edge hhead hit side).mpr hreturn) hshape

end PushPuzzle.PushS.Comb

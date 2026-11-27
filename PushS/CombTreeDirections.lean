/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PreparedRayOrder
public import PushS.CombTeeth
public import PushS.CombSpine
import all PushS.CombTeeth
import all PushS.CombSpine

/-! The actual comb-tree germs have their literal vertical or horizontal clockwise octants. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem octant_down : octantAngle 2 = ((-(Real.pi / 2) : ℝ) : Real.Angle) := by
  change ((-(2 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle) = _
  congr 1
  ring

private theorem octant_up : octantAngle 6 = ((Real.pi / 2 : ℝ) : Real.Angle) := by
  change ((-(6 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle) = _
  rw [show (-(6 : ℝ) * Real.pi / 4) = Real.pi / 2 - 2 * Real.pi by ring]
  simp only [Real.Angle.coe_sub, Real.Angle.coe_two_pi, sub_zero]

private theorem octant_left : octantAngle 4 = (Real.pi : Real.Angle) := by
  change ((-(4 : ℝ) * Real.pi / 4 : ℝ) : Real.Angle) = _
  rw [show (-(4 : ℝ) * Real.pi / 4) = -Real.pi by ring, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]

private theorem octant_right : octantAngle 0 = 0 := by simp [octantAngle]

private theorem tooth_germ_coordinates (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool) :
    ((toothPiece width d vertex piece).germ side).re = 0 ∧
      (if side then ((toothPiece width d vertex piece).germ side).im < 0
        else 0 < ((toothPiece width d vertex piece).germ side).im) := by
  have hxlo := toothStation_column width d vertex piece.castSucc
  have hxhi := toothStation_column width d vertex piece.succ
  have hy := toothStation_strictMono width height hd hfit vertex
    (a := piece.castSucc) (b := piece.succ) Fin.castSucc_lt_succ
  cases side with
  | false =>
    change (complexPoint (stationPoint width d (toothStation width d vertex piece.succ)) -
      complexPoint (stationPoint width d (toothStation width d vertex piece.castSucc))).re = 0 ∧ _
    constructor
    · change ((stationPoint width d (toothStation width d vertex piece.succ)).1 : ℝ) -
        ((stationPoint width d (toothStation width d vertex piece.castSucc)).1 : ℝ) = 0
      rw [hxlo, hxhi, sub_self]
    · change 0 < ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) -
        ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ)
      exact_mod_cast sub_pos.mpr hy
  | true =>
    change (complexPoint (stationPoint width d (toothStation width d vertex piece.castSucc)) -
      complexPoint (stationPoint width d (toothStation width d vertex piece.succ))).re = 0 ∧ _
    constructor
    · change ((stationPoint width d (toothStation width d vertex piece.castSucc)).1 : ℝ) -
        ((stationPoint width d (toothStation width d vertex piece.succ)).1 : ℝ) = 0
      rw [hxlo, hxhi, sub_self]
    · change ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) -
        ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) < 0
      exact_mod_cast sub_neg.mpr hy

/-- Every genuine tooth-piece end has exactly its actual upward or downward ray direction. -/
theorem toothPiece_direction (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool) :
    (((toothPiece width d vertex piece).germ side).arg : Real.Angle) = octantAngle (if side then 2 else 6) := by
  have h := tooth_germ_coordinates width height hd hfit vertex piece side
  cases side with
  | false =>
    rw [show ((toothPiece width d vertex piece).germ false).arg = Real.pi / 2 from Complex.arg_eq_pi_div_two_iff.mpr h]
    exact octant_up.symm
  | true =>
    rw [show ((toothPiece width d vertex piece).germ true).arg = -(Real.pi / 2) from Complex.arg_eq_neg_pi_div_two_iff.mpr h]
    exact octant_down.symm

private theorem spine_germ_coordinates (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (side : Bool) :
    ((spinePiece width d piece).germ side).im = 0 ∧
      (if side then ((spinePiece width d piece).germ side).re < 0 else 0 < ((spinePiece width d piece).germ side).re) := by
  have hx := spine_columns_strict width height hd hfit piece
  cases side with
  | false =>
    change (complexPoint (stationPoint width d (.foot (spineRight width d piece))) -
      complexPoint (stationPoint width d (.foot (spineLeft width d piece)))).im = 0 ∧ _
    constructor
    · change (((-2 : ℤ) : ℝ) - ((-2 : ℤ) : ℝ)) = 0
      exact sub_self _
    · change 0 < (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) -
        (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ)
      exact_mod_cast sub_pos.mpr hx
  | true =>
    change (complexPoint (stationPoint width d (.foot (spineLeft width d piece))) -
      complexPoint (stationPoint width d (.foot (spineRight width d piece)))).im = 0 ∧ _
    constructor
    · change (((-2 : ℤ) : ℝ) - ((-2 : ℤ) : ℝ)) = 0
      exact sub_self _
    · change (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) -
        (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) < 0
      exact_mod_cast sub_neg.mpr hx

/-- Every genuine spine-piece end has exactly its actual rightward or leftward ray direction. -/
theorem spinePiece_direction (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (side : Bool) :
    (((spinePiece width d piece).germ side).arg : Real.Angle) = octantAngle (if side then 4 else 0) := by
  have h := spine_germ_coordinates width height hd hfit piece side
  cases side with
  | false =>
    rw [show ((spinePiece width d piece).germ false).arg = 0 from Complex.arg_eq_zero_iff.mpr ⟨h.2.le, h.1⟩]
    exact octant_right.symm
  | true =>
    rw [show ((spinePiece width d piece).germ true).arg = Real.pi from Complex.arg_eq_pi_iff.mpr ⟨h.2, h.1⟩]
    exact octant_left.symm

end PushPuzzle.PushS.Comb

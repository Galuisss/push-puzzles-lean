/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombFragmentGerms
import all PushS.CombFragmentGerms
import all PushS.CombPreprocess

/-! The actual geometric source rays agree with the compiler's original prepared tangent vectors. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem complexPoint_sub (a b : Point) : complexPoint (a - b) = complexPoint a - complexPoint b := by
  apply Complex.ext
  · change ((a.1 - b.1 : ℤ) : ℝ) = (a.1 : ℝ) - b.1
    exact Int.cast_sub _ _
  · change ((a.2 - b.2 : ℤ) : ℝ) = (a.2 : ℝ) - b.2
    exact Int.cast_sub _ _

private theorem prepared_route_getD (width : ℕ) (d : Graph.OrthogonalDrawing) (edge index : ℕ) :
    ((prepare width d).2.getD edge []).getD index (0, 0) = point width ((d.2.getD edge []).getD index (0, 0)) := by
  rw [route_prepare]
  simpa only [point, mul_zero, add_zero] using
    (List.getD_map (l := d.2.getD edge []) (d := (0, 0)) (n := index) (point width))

/-- The native source drawing's prepared endpoint ray is exactly the compiler's original outgoing vector. -/
theorem preparedRoute_germ_outgoing (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (side : Bool) :
    (preparedRoute width hd edge).germ side = complexPoint (outgoingVector width d ⟨edge.val, side⟩) := by
  have hlen : 2 ≤ (d.2.getD edge []).length := by
    have h := Graph.OrthogonalDrawing.sourceRoute_length_ge_two hd edge.isLt
    have he := congrArg List.length (sourceRoute_reverse_eq_raw hd edge hhead)
    simp only [List.length_reverse] at he
    omega
  have hprepared : ((prepare width d).2.getD edge []).length = (d.2.getD edge []).length := by
    rw [route_prepare]
    simp only [List.length_map]
  cases side with
  | false =>
    change (preparedRoute width hd edge).point (0 : Fin (preparedRoute width hd edge).segments).succ -
      (preparedRoute width hd edge).point 0 = _
    rw [preparedRoute_point_raw width hd edge hhead, preparedRoute_point_raw width hd edge hhead]
    simp only [outgoingVector, Bool.false_eq_true, ite_false]
    rw [prepared_route_getD, prepared_route_getD, ← complexPoint_sub]
    rfl
  | true =>
    change (preparedRoute width hd edge).point (Fin.last (preparedRoute width hd edge).bends).castSucc -
      (preparedRoute width hd edge).point (Fin.last ((preparedRoute width hd edge).bends + 1)) = _
    rw [preparedRoute_point_raw width hd edge hhead, preparedRoute_point_raw width hd edge hhead]
    simp only [outgoingVector, ite_true]
    rw [List.getD_reverse 1 (by omega), List.getD_reverse 0 (by omega),
      prepared_route_getD, prepared_route_getD, ← complexPoint_sub]
    simp only [Fin.val_castSucc, Fin.val_last, preparedRoute_bends_raw width hd edge hhead, hprepared]
    have hi : (d.2.getD edge []).length - 2 + 1 = (d.2.getD edge []).length - 1 := by omega
    have hj : (d.2.getD edge []).length - 1 - 1 = (d.2.getD edge []).length - 2 := by omega
    rw [hi, hj, Nat.sub_zero]

/-- Each actual native fragment incidence has exactly the outgoing direction used by the original fan compiler. -/
theorem edgeFragment_native_arg (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (side : Bool) :
    ((edgeFragment width height hd hfit edge hhead
      (if side then Fin.last (edgeCrossings width d edge).length else 0)).germ side).arg =
        (complexPoint (outgoingVector width d ⟨edge.val, side⟩)).arg := by
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [edgeFragment_start_arg, preparedRoute_germ_outgoing width hd edge hhead false]
  | true =>
    simp only [ite_true]
    rw [edgeFragment_finish_arg, preparedRoute_germ_outgoing width hd edge hhead true]

end PushPuzzle.PushS.Comb

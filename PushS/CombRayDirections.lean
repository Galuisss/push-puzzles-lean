/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCrossingGerms
public import PushS.CombNativeGerms
import all PushS.CombCrossingParameter
import all PushS.CombPreprocess

/-! Every actual source ray is horizontal or has the literal prepared diagonal slope one. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

private theorem prepared_segment_pair (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (index : Fin (preparedRoute width hd edge).segments) :
    ∃ ab ∈ ((prepare width d).2.getD edge []).consecutivePairs,
      (preparedRoute width hd edge).point index.castSucc = complexPoint ab.1 ∧
      (preparedRoute width hd edge).point index.succ = complexPoint ab.2 := by
  have hlen : 2 ≤ (d.2.getD edge []).length := by
    simpa only [Graph.OrthogonalDrawing.length_sourceRoute] using
      Graph.OrthogonalDrawing.sourceRoute_length_ge_two hd edge.isLt
  have hi : index.val + 1 < ((prepare width d).2.getD edge []).length := by
    have h := index.isLt
    change index.val < (preparedRoute width hd edge).bends + 1 at h
    rw [preparedRoute_bends_raw width hd edge hhead] at h
    rw [route_prepare, List.length_map]
    omega
  let ab := (((prepare width d).2.getD edge []).getD index.val (0, 0),
    ((prepare width d).2.getD edge []).getD (index.val + 1) (0, 0))
  have hab : ab ∈ ((prepare width d).2.getD edge []).consecutivePairs := by
    dsimp only [ab]
    rw [List.getD_eq_getElem ((prepare width d).2.getD edge []) (0, 0) (by omega : index.val < _),
      List.getD_eq_getElem ((prepare width d).2.getD edge []) (0, 0) hi]
    exact List.getElem_mem_consecutivePairs _ index.val hi
  have hl := preparedRoute_point_raw width hd edge hhead index.castSucc
  have hr := preparedRoute_point_raw width hd edge hhead index.succ
  change _ = complexPoint (point width ((d.2.getD edge []).getD index.val (0, 0))) at hl
  change _ = complexPoint (point width ((d.2.getD edge []).getD (index.val + 1) (0, 0))) at hr
  rw [← point_route_prepare width d edge index.val] at hl
  rw [← point_route_prepare width d edge (index.val + 1)] at hr
  exact ⟨ab, hab, hl, hr⟩

/-- Every actual original prepared segment has precisely horizontal or diagonal slope one. -/
theorem preparedRoute_segment_shape (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (index : Fin (preparedRoute width hd edge).segments) :
    ((preparedRoute width hd edge).point index.succ - (preparedRoute width hd edge).point index.castSucc).im = 0 ∨
      ((preparedRoute width hd edge).point index.succ - (preparedRoute width hd edge).point index.castSucc).im =
        ((preparedRoute width hd edge).point index.succ - (preparedRoute width hd edge).point index.castSucc).re := by
  obtain ⟨ab, hab, hl, hr⟩ := prepared_segment_pair width hd edge hhead index
  have hshape := map_segment_slopes width (hd.orthogonal edge edge.isLt) ab (by simpa only [route_prepare] using hab)
  rw [hl, hr]
  rcases hshape with hh | hd
  · left
    change (ab.2.2 : ℝ) - ab.1.2 = 0
    exact_mod_cast (show ab.2.2 - ab.1.2 = 0 by omega)
  · right
    change (ab.2.2 : ℝ) - ab.1.2 = (ab.2.1 : ℝ) - ab.1.1
    exact_mod_cast (show ab.2.2 - ab.1.2 = ab.2.1 - ab.1.1 by omega)

/-- Every actual crossing fragment germ has horizontal or diagonal slope one. -/
theorem edgeFragment_crossing_shape (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).im = 0 ∨
      ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).im =
        ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).re := by
  obtain ⟨original, scale, _, _, hg⟩ := edgeFragment_crossing_germ width height hd hfit edge hhead hit side
  have hshape := preparedRoute_segment_shape width hd edge hhead original
  rw [hg]
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Complex.smul_re, Complex.smul_im]
    rcases hshape with hh | hd
    · exact Or.inl (by rw [hh]; simp)
    · exact Or.inr (by rw [hd])
  | true =>
    simp only [ite_true, Complex.smul_re, Complex.smul_im]
    have hneg : (preparedRoute width hd edge).point original.castSucc - (preparedRoute width hd edge).point original.succ =
        -((preparedRoute width hd edge).point original.succ - (preparedRoute width hd edge).point original.castSucc) := by abel
    rw [hneg]
    simp only [Complex.neg_re, Complex.neg_im]
    rcases hshape with hh | hd
    · exact Or.inl (by rw [hh]; simp)
    · exact Or.inr (by rw [hd])

private theorem neg_shape {z : ℂ} (h : z.im = 0 ∨ z.im = z.re) :
    (-z).im = 0 ∨ (-z).im = (-z).re := by
  rcases h with hh | hd
  · exact Or.inl (by simp [hh])
  · exact Or.inr (by simp [hd])

/-- Every actual original source endpoint ray has horizontal or diagonal slope one. -/
theorem preparedRoute_germ_shape (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (side : Bool) :
    ((preparedRoute width hd edge).germ side).im = 0 ∨
      ((preparedRoute width hd edge).germ side).im = ((preparedRoute width hd edge).germ side).re := by
  cases side with
  | false =>
    simpa only [Cslib.Polygonal.Route.germ, Bool.false_eq_true, ite_false, Cslib.Polygonal.Route.start, Fin.castSucc_zero] using
      preparedRoute_segment_shape width hd edge hhead 0
  | true =>
    simpa only [Cslib.Polygonal.Route.germ, ite_true, Cslib.Polygonal.Route.finish, Fin.succ_last, neg_sub] using
      neg_shape (preparedRoute_segment_shape width hd edge hhead (Fin.last (preparedRoute width hd edge).bends))

/-- Every actual source endpoint ray has a strictly nonzero horizontal component. -/
theorem preparedRoute_germ_re_ne_zero (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) :
    ((preparedRoute width hd edge).germ side).re ≠ 0 := by
  cases side with
  | false =>
    have h := preparedDrawing_segment_nonvertical width hd edge 0
    change ((preparedRoute width hd edge).point (0 : Fin (preparedRoute width hd edge).segments).castSucc).re ≠
      ((preparedRoute width hd edge).point (0 : Fin (preparedRoute width hd edge).segments).succ).re at h
    exact sub_ne_zero.mpr h.symm
  | true =>
    have h := preparedDrawing_segment_nonvertical width hd edge (Fin.last (preparedRoute width hd edge).bends)
    change ((preparedRoute width hd edge).point (Fin.last (preparedRoute width hd edge).bends).castSucc).re ≠
      ((preparedRoute width hd edge).point (Fin.last (preparedRoute width hd edge).bends).succ).re at h
    exact sub_ne_zero.mpr h

/-- The literal integer compiler tangent belongs to exactly the prepared horizontal/diagonal ray families. -/
theorem outgoingVector_shape (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (side : Bool) :
    (outgoingVector width d ⟨edge.val, side⟩).2 = 0 ∨
      (outgoingVector width d ⟨edge.val, side⟩).2 = (outgoingVector width d ⟨edge.val, side⟩).1 := by
  have h := preparedRoute_germ_shape width hd edge hhead side
  rw [preparedRoute_germ_outgoing width hd edge hhead side] at h
  change ((outgoingVector width d ⟨edge.val, side⟩).2 : ℝ) = 0 ∨
    ((outgoingVector width d ⟨edge.val, side⟩).2 : ℝ) = ((outgoingVector width d ⟨edge.val, side⟩).1 : ℝ) at h
  exact_mod_cast h

/-- The native compiler tangent always has a nonzero horizontal coordinate in a genuine source drawing. -/
theorem outgoingVector_x_ne_zero (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (side : Bool) :
    (outgoingVector width d ⟨edge.val, side⟩).1 ≠ 0 := by
  have h := preparedRoute_germ_re_ne_zero width hd edge side
  rw [preparedRoute_germ_outgoing width hd edge hhead side] at h
  change ((outgoingVector width d ⟨edge.val, side⟩).1 : ℝ) ≠ 0 at h
  exact_mod_cast h

end PushPuzzle.PushS.Comb

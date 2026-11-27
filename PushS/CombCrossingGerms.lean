/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombEdgeStations
public import PushS.PolygonalInteriorGerms

/-! The actual two fragment rays at each emitted crossing retain the strict original segment ray. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The exact global crossing occurrence stored at one actual source-edge encounter index. -/
@[expose] def edgeCrossingHit (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (hit : Fin (edgeCrossings width d edge).length) : {c // c ∈ crossings width d} :=
  ⟨(edgeCrossings width d edge).get hit, by
    exact (List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp (List.get_mem _ hit))).1⟩

/-- Each indexed actual encounter retains its original source edge identity. -/
theorem edgeCrossingHit_edge (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ)
    (hit : Fin (edgeCrossings width d edge).length) : (edgeCrossingHit width d edge hit).val.edge = edge := by
  have h := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp (List.get_mem _ hit))
  exact of_decide_eq_true h.2

/-- The corresponding literal original-edge station is exactly the same global crossing occurrence. -/
theorem edgeStation_crossing (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : Fin (edgeCrossings width d edge).length) :
    edgeStation width hd edge hit.succ.castSucc = .crossing (edgeCrossingHit width d edge hit) := by
  simp only [edgeStation, edgeStations, List.get_eq_getElem, Fin.val_castSucc, Fin.val_succ,
    List.cons_append, List.getElem_cons_succ]
  rw [List.getElem_append_left (by simpa only [List.length_map, List.length_attach] using hit.isLt)]
  simp only [List.getElem_map, List.getElem_attach]
  rfl

/-- The preceding and following real fragment ends occupy precisely the same original crossing point. -/
theorem edgeFragment_crossing_endpoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    (edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).endpoint side =
      complexPoint ((edgeCrossingHit width d edge hit).val.location width d) := by
  rw [edgeFragment_station_endpoint]
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [edgeStation_crossing]
    rfl
  | true =>
    simp only [ite_true, Fin.succ_castSucc]
    rw [edgeStation_crossing]
    rfl

/-- Each real outgoing fragment ray at an emitted crossing is a positive multiple of its original source-segment ray. -/
theorem edgeFragment_crossing_germ (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    ∃ (original : Fin (preparedRoute width hd edge).segments) (scale : ℝ),
      original.val = (edgeCrossingHit width d edge hit).val.segment ∧ 0 < scale ∧
      (edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side =
        scale • (if side then (preparedRoute width hd edge).point original.castSucc - (preparedRoute width hd edge).point original.succ
          else (preparedRoute width hd edge).point original.succ - (preparedRoute width hd edge).point original.castSucc) := by
  have hglobal := (edgeCrossingHit width d edge hit).property
  have hedge : edge.val = (edgeCrossingHit width d edge hit).val.edge := (edgeCrossingHit_edge width d edge hit).symm
  obtain ⟨original, parameter, hi, ht, hp⟩ := crossing_prepared_parameter width hd edge hhead hglobal hedge
  let piece := if side then hit.castSucc else hit.succ
  have he : (edgeFragment width height hd hfit edge hhead piece).endpoint side =
      (preparedRoute width hd edge).eval original parameter :=
    (edgeFragment_crossing_endpoint width height hd hfit edge hhead hit side).trans hp.symm
  obtain ⟨scale, hscale, hg⟩ := PushPuzzle.Polygonal.Route.subroute_germ_mapAtCuts_interior
    ((preparedDrawing_isEmbedding width hd).simple edge) (preparedDrawing_route_open width hd edge)
    (toothLevels width d) Complex.reCLM.toLinearMap.toAffineMap
    (edgeCutNode width hd edge piece.castSucc) (edgeCutNode width hd edge piece.succ)
    (edgeCutNode_strictMono width height hd hfit edge hhead Fin.castSucc_lt_succ) side original ht he
  exact ⟨original, scale, hi, hscale, hg⟩

/-- The actual outgoing ray points right exactly when its original crossing-side token is the return-side token. -/
theorem edgeFragment_crossing_re_pos (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    0 < ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).re ↔
      (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) = true := by
  obtain ⟨original, scale, hi, hscale, hg⟩ := edgeFragment_crossing_germ width height hd hfit edge hhead hit side
  have hdir := crossing_prepared_direction width hd edge hhead (edgeCrossingHit width d edge hit).property
    (edgeCrossingHit_edge width d edge hit).symm original hi
  have hne := preparedDrawing_segment_nonvertical width hd edge original
  have hreal := congrArg Complex.re hg
  simp only [Complex.smul_re] at hreal
  cases hforward : (edgeCrossingHit width d edge hit).val.forward with
  | false =>
    have hnot : ¬((preparedRoute width hd edge).point original.castSucc).re <
        ((preparedRoute width hd edge).point original.succ).re := by rw [← hdir, hforward]; simp
    have hneg := lt_of_le_of_ne (not_lt.mp hnot) hne.symm
    have hprod := mul_pos hscale (sub_pos.mpr hneg)
    cases side <;> simp only [Bool.false_eq_true, Bool.not_false, ite_false, ite_true, iff_true, iff_false,
      Complex.sub_re, smul_eq_mul] at hreal ⊢ <;>
      nlinarith
  | true =>
    have hpos := hdir.mp hforward
    have hprod := mul_pos hscale (sub_pos.mpr hpos)
    cases side <;> simp only [Bool.false_eq_true, Bool.not_true, ite_false, ite_true, iff_true, iff_false,
      Complex.sub_re, smul_eq_mul] at hreal ⊢ <;>
      nlinarith

/-- Every actual crossing fragment ray has a strictly nonzero horizontal component. -/
theorem edgeFragment_crossing_re_ne_zero (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).re ≠ 0 := by
  obtain ⟨original, scale, _, hscale, hg⟩ := edgeFragment_crossing_germ width height hd hfit edge hhead hit side
  have hne := preparedDrawing_segment_nonvertical width hd edge original
  change ((preparedRoute width hd edge).point original.castSucc).re ≠
    ((preparedRoute width hd edge).point original.succ).re at hne
  intro he
  have hreal := congrArg Complex.re hg
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false, Complex.smul_re, Complex.sub_re, smul_eq_mul] at he hreal
    rw [he] at hreal
    exact mul_ne_zero (ne_of_gt hscale) (sub_ne_zero.mpr hne.symm) hreal.symm
  | true =>
    simp only [ite_true, Complex.smul_re, Complex.sub_re, smul_eq_mul] at he hreal
    rw [he] at hreal
    exact mul_ne_zero (ne_of_gt hscale) (sub_ne_zero.mpr hne) hreal.symm

/-- The actual outgoing ray points left exactly when its original crossing-side token is the ascending-side token. -/
theorem edgeFragment_crossing_re_neg (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : Fin (edgeCrossings width d edge).length) (side : Bool) :
    ((edgeFragment width height hd hfit edge hhead (if side then hit.castSucc else hit.succ)).germ side).re < 0 ↔
      (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) = false := by
  have hpos := edgeFragment_crossing_re_pos width height hd hfit edge hhead hit side
  have hne := edgeFragment_crossing_re_ne_zero width height hd hfit edge hhead hit side
  cases hreturn : (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) with
  | false =>
    simp only [hreturn, Bool.false_eq_true, iff_false, iff_true] at hpos ⊢
    exact lt_of_le_of_ne (not_lt.mp hpos) hne
  | true =>
    simp only [hreturn, Bool.true_eq_false, iff_true, iff_false] at hpos ⊢
    exact not_lt.mpr hpos.le

end PushPuzzle.PushS.Comb

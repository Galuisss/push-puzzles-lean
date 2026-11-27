/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCrossingGeometry
import all PushS.CombPreprocess
import all PushS.CombCrossingGeometry
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-! Every genuine source-route contact below an actual tooth tip is in the literal crossing scan. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

private theorem point_column_is_site (width height : ℕ) {d : Graph.OrthogonalDrawing}
    (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length) (q : Point)
    (hq : 0 ≤ q.1 ∧ q.1 ≤ width)
    (hx : (point width q).1 = ((prepare width d).1.getD vertex (0, 0)).1) :
    point width q = (prepare width d).1.getD vertex (0, 0) := by
  have hm : d.1.getD vertex (0, 0) ∈ d.1 := by
    rw [List.getD_eq_getElem _ _ vertex.isLt]
    exact List.getElem_mem vertex.isLt
  have hv := hfit.1 _ hm
  rw [site_prepare] at hx ⊢
  exact congrArg (point width) (point_column_injective width hq ⟨hv.1, hv.2.1⟩ hx)

private theorem route_point_column_is_site (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) (vertex : Fin d.1.length) {q : Point}
    (hq : q ∈ (prepare width d).2.getD edge [])
    (hx : q.1 = ((prepare width d).1.getD vertex (0, 0)).1) : q = (prepare width d).1.getD vertex (0, 0) := by
  rw [route_prepare] at hq
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
  have hi : edge.val < d.2.length := by rw [hd.edgeCount]; exact edge.isLt
  have hr : d.2.getD edge [] ∈ d.2 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hbound := hfit.2 _ hr p hp
  exact point_column_is_site width height hfit vertex p ⟨hbound.1, hbound.2.1⟩ hx

private theorem below_tip_not_route_point (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) (vertex : Fin d.1.length) {z : ℝ × ℝ}
    (hx : z.1 = (((prepare width d).1.getD vertex (0, 0)).1 : ℝ))
    (hy : z.2 < (((prepare width d).1.getD vertex (0, 0)).2 : ℝ))
    {q : Point} (hq : q ∈ (prepare width d).2.getD edge []) : z ≠ realPoint q := by
  intro he
  have hcol : q.1 = ((prepare width d).1.getD vertex (0, 0)).1 := by
    have h := congrArg Prod.fst he
    change z.1 = (q.1 : ℝ) at h
    exact_mod_cast h.symm.trans hx
  have hq' := route_point_column_is_site width height hd hfit edge vertex hq hcol
  rw [he, hq'] at hy
  exact (lt_irrefl _ hy)

private theorem segment_interior_below_tip (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) (vertex : Fin d.1.length) {ab : Point × Point}
    (hab : ab ∈ ((prepare width d).2.getD edge []).consecutivePairs) {z : ℝ × ℝ}
    (hz : z ∈ Orthogonal.segment ab.1 ab.2)
    (hx : z.1 = (((prepare width d).1.getD vertex (0, 0)).1 : ℝ))
    (hy : z.2 < (((prepare width d).1.getD vertex (0, 0)).2 : ℝ)) :
    min ab.1.1 ab.2.1 < ((prepare width d).1.getD vertex (0, 0)).1 ∧
      ((prepare width d).1.getD vertex (0, 0)).1 < max ab.1.1 ab.2.1 := by
  have hm := List.of_mem_zip hab
  have hs := map_segment_slopes width (hd.orthogonal edge edge.isLt) ab
  rw [route_prepare] at hab
  have hshape := hs hab
  have hb := (segment_column_iff ab.1 ab.2 hshape _ z hx).mp hz
  have hne0 : z ≠ realPoint ab.1 := below_tip_not_route_point width height hd hfit edge vertex hx hy hm.1
  have hne1 : z ≠ realPoint ab.2 := below_tip_not_route_point width height hd hfit edge vertex hx hy
    (List.mem_of_mem_tail hm.2)
  have hl : ab.1.1 ≠ ((prepare width d).1.getD vertex (0, 0)).1 := by
    intro he
    apply hne0
    exact (eq_cutPoint_of_mem_segment ab.1 ab.2 hshape _ hz hx).trans
      (eq_cutPoint_of_mem_segment ab.1 ab.2 hshape _ (left_mem_segment ℝ _ _) (by
        change (ab.1.1 : ℝ) = _
        exact_mod_cast he)).symm
  have hr : ab.2.1 ≠ ((prepare width d).1.getD vertex (0, 0)).1 := by
    intro he
    apply hne1
    exact (eq_cutPoint_of_mem_segment ab.1 ab.2 hshape _ hz hx).trans
      (eq_cutPoint_of_mem_segment ab.1 ab.2 hshape _ (right_mem_segment ℝ _ _) (by
        change (ab.2.1 : ℝ) = _
        exact_mod_cast he)).symm
  omega

/-- Every genuine source-route point below an actual tooth tip is in the literal crossing table. -/
theorem crossing_exists_below_tip (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) (vertex : Fin d.1.length) {z : ℝ × ℝ}
    (hz : z ∈ support ((prepare width d).2.getD edge []))
    (hx : z.1 = (((prepare width d).1.getD vertex (0, 0)).1 : ℝ))
    (hy : z.2 < (((prepare width d).1.getD vertex (0, 0)).2 : ℝ)) :
    ∃ c ∈ crossings width d, c.edge = edge.val ∧ c.vertex = vertex.val ∧ z = realPoint (c.location width d) := by
  rcases hz with ⟨q, hq, hpoint⟩ | ⟨ab, hab, hz⟩
  · exact False.elim (below_tip_not_route_point width height hd hfit edge vertex hx hy hq hpoint)
  · have hstrict := segment_interior_below_tip width height hd hfit edge vertex hab hz hx hy
    have hsrc : ab ∈ ((d.2.getD edge []).map (point width)).consecutivePairs := by
      simpa only [route_prepare] using hab
    have hshape := map_segment_slopes width (hd.orthogonal edge edge.isLt) ab hsrc
    have hcoord := (segment_column_iff ab.1 ab.2 hshape _ z hx).mp hz
    obtain ⟨j, hj⟩ := List.mem_iff_get.mp hab
    let site := (prepare width d).1.getD vertex (0, 0)
    have hstrict' : min ab.1.1 ab.2.1 < site.1 ∧ site.1 < max ab.1.1 ab.2.1 := hstrict
    let c : Crossing := ⟨edge.val, j.val, vertex.val, cutHeight ab.1 ab.2 site.1, decide (ab.1.1 < ab.2.1)⟩
    have hedge : edge.val < (prepare width d).2.length := by
      simpa only [prepare, List.length_map, hd.edgeCount] using edge.isLt
    have hvert : vertex.val < (prepare width d).1.length := by
      simpa only [prepare, List.length_map] using vertex.isLt
    have hr : (prepare width d).2[edge.val]? = some ((prepare width d).2.getD edge []) := by
      rw [List.getElem?_eq_getElem hedge, List.getD_eq_getElem _ _ hedge]
    have hv : (prepare width d).1[vertex.val]? = some site := by
      rw [List.getElem?_eq_getElem hvert]
      dsimp only [site]
      rw [List.getD_eq_getElem _ _ hvert]
    have hab' : ((prepare width d).2.getD edge []).consecutivePairs[j.val]? = some ab := by
      rw [List.getElem?_eq_getElem j.isLt]
      exact congrArg some hj
    have hheight : cutHeight ab.1 ab.2 site.1 < site.2 := by
      rw [hcoord.1] at hy
      exact_mod_cast hy
    have hc : c ∈ crossings width d := by
      apply (mem_crossings_iff width d c).mpr
      exact ⟨_, ab, site, hr, hab', hv, ⟨by omega, hheight⟩, rfl, rfl⟩
    exact ⟨c, hc, rfl, rfl, Prod.ext hx hcoord.1⟩

/-- That actual continuous source/tooth contact identifies one complete crossing occurrence. -/
theorem crossing_unique_below_tip (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) (vertex : Fin d.1.length) {z : ℝ × ℝ}
    (hz : z ∈ support ((prepare width d).2.getD edge []))
    (hx : z.1 = (((prepare width d).1.getD vertex (0, 0)).1 : ℝ))
    (hy : z.2 < (((prepare width d).1.getD vertex (0, 0)).2 : ℝ)) :
    ∃! c : Crossing, c ∈ crossings width d ∧ c.edge = edge.val ∧ c.vertex = vertex.val ∧
      z = realPoint (c.location width d) := by
  obtain ⟨c, hc, he, hv, hp⟩ := crossing_exists_below_tip width height hd hfit edge vertex hz hx hy
  refine ⟨c, ⟨hc, he, hv, hp⟩, ?_⟩
  intro c' hc'
  apply crossing_location_injective width hd (fun p hp => ⟨(hfit.1 p hp).1, (hfit.1 p hp).2.1⟩) hc'.1 hc
  exact realPoint_injective (hc'.2.2.2.symm.trans hp)

end PushPuzzle.PushS.Comb

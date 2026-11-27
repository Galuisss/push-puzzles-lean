/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombFragments
public import PushS.CombStations
import all PushS.CombFragments
import all PushS.PolygonalSubroute

/-! Actual original-edge fragments retain their exact native tip and crossing station names. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The same original source endpoint, as its actual indexed tooth tip. -/
@[expose] def edgeTipStation (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) : Station width d :=
  .tip ⟨G.vertices.idxOf (Graph.Dart.vertex (edge, side)), by
    rw [hd.vertexCount]
    apply List.idxOf_lt_length_of_mem
    have h := hd.endpointsDeclared G.edges[edge] (List.getElem_mem edge.isLt)
    rw [Graph.Dart.edge_eq_vertices edge] at h
    cases side
    · exact h.1
    · exact h.2⟩

private theorem edgeTipStation_point (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) :
    complexPoint (stationPoint width d (edgeTipStation width hd edge side)) =
      ((refinedDrawing width hd).route edge).endpoint side := by
  rw [(refinedDrawing width hd).endpoint_eq]
  exact (preparedDrawing_vertex width hd _).symm

/-- The complete actual station sequence encountered on one original directed source edge. -/
@[expose] def edgeStations (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) : List (Station width d) :=
  edgeTipStation width hd edge false ::
    (edgeCrossings width d edge).attach.map (fun hit => .crossing ⟨hit.val, by
      exact (List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hit.property)).1⟩) ++
    [edgeTipStation width hd edge true]

/-- Actual original tips add exactly two stations to the source edge's actual crossing list. -/
theorem edgeStations_length (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    (edgeStations width hd edge).length = (edgeCrossings width d edge).length + 2 := by
  simp only [edgeStations, List.length_cons, List.length_append, List.length_map,
    List.length_attach, List.length_nil]

/-- Every genuine crossing on an original edge has its exact name in that edge's station array. -/
theorem crossing_mem_edgeStations (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : {c // c ∈ crossings width d}) (he : hit.val.edge = edge.val) :
    Station.crossing hit ∈ edgeStations width hd edge := by
  apply List.mem_append_left
  apply List.mem_cons_of_mem
  apply List.mem_map.mpr
  have hc : hit.val ∈ edgeCrossings width d edge :=
    (edgeCrossings_perm width d edge).mem_iff.mpr (List.mem_filter.mpr ⟨hit.property, by simp [he]⟩)
  exact ⟨⟨hit.val, hc⟩, List.mem_attach _ _, rfl⟩

/-- These actual named stations are exactly the geometric nodes of the original-edge cut list. -/
theorem edgeStations_points (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    (edgeStations width hd edge).map (fun station => complexPoint (stationPoint width d station)) =
      (edgeCutNodes width hd edge).map ((refinedDrawing width hd).route edge).point := by
  simp only [edgeStations, edgeCutNodes, List.map_cons, List.map_append, List.map_nil, List.map_map]
  apply congrArg₂ (fun (a b : List ℂ) => a ++ b)
  · apply List.cons_eq_cons.mpr
    refine ⟨edgeTipStation_point width hd edge false, ?_⟩
    apply List.map_congr_left
    intro hit _
    exact (edgeCrossingNode_point width hd edge hit).symm
  · exact congrArg (fun z => [z]) (edgeTipStation_point width hd edge true)

/-- Select a named station at its literal position on the original source edge. -/
@[expose] def edgeStation (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (index : Fin ((edgeCrossings width d edge).length + 2)) : Station width d :=
  (edgeStations width hd edge).get ⟨index.val, by rw [edgeStations_length]; exact index.isLt⟩

/-- The selected actual source station is exactly the corresponding genuine refined route node. -/
theorem edgeStation_point (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (index : Fin ((edgeCrossings width d edge).length + 2)) :
    complexPoint (stationPoint width d (edgeStation width hd edge index)) =
      ((refinedDrawing width hd).route edge).point (edgeCutNode width hd edge index) := by
  have h := congrArg (fun points : List ℂ => points[index.val]?) (edgeStations_points width hd edge)
  have hs : index.val < (edgeStations width hd edge).length := by rw [edgeStations_length]; exact index.isLt
  have hc : index.val < (edgeCutNodes width hd edge).length := by rw [edgeCutNodes_length]; exact index.isLt
  simp only [List.getElem?_map, List.getElem?_eq_getElem hs, List.getElem?_eq_getElem hc, Option.map_some] at h
  exact Option.some.inj h

/-- Each original-edge fragment ends at its own exact named source stations. -/
theorem edgeFragment_station_endpoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    (edgeFragment width height hd hfit edge hhead piece).endpoint side =
      complexPoint (stationPoint width d (edgeStation width hd edge (if side then piece.succ else piece.castSucc))) := by
  rw [edgeFragment_endpoint, edgeStation_point]

/-- A genuine source fragment meets any station of its original edge only at its own named ends. -/
theorem edgeFragment_cut_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (cut : Fin ((edgeCrossings width d edge).length + 2))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i t =
      complexPoint (stationPoint width d (edgeStation width hd edge cut))) :
    ∃ side, (edgeFragment width height hd hfit edge hhead piece).AtEnd i t side ∧
      cut = if side then piece.succ else piece.castSucc := by
  rw [edgeStation_point] at he
  exact (PushPuzzle.Polygonal.Route.IsSimple.subroute_cut_contact ((refinedDrawing_isEmbedding width hd).simple edge))
    (refined_route_open width hd edge) (edgeCutNode width hd edge)
    (edgeCutNode_strictMono width height hd hfit edge hhead) piece cut i ht he

private theorem crossing_ne_refined_endpoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (hit : {c // c ∈ crossings width d}) (edge : Fin G.edges.length) (side : Bool) :
    complexPoint (hit.val.location width d) ≠ ((refinedDrawing width hd).route edge).endpoint side := by
  intro he
  have hp : stationPoint width d (.crossing hit) = stationPoint width d (edgeTipStation width hd edge side) :=
    complexPoint_injective (he.trans (edgeTipStation_point width hd edge side).symm)
  have hs := stationPoint_injective width height hd hfit hp
  change Station.crossing hit = Station.tip _ at hs
  cases hs

private theorem fragment_crossing_edge (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hit : {c // c ∈ crossings width d})
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i t = complexPoint (hit.val.location width d)) :
    hit.val.edge = edge.val := by
  have hi : hit.val.edge < G.edges.length := by rw [← hd.edgeCount]; exact crossing_edge_lt width d hit.property
  let other : Fin G.edges.length := ⟨hit.val.edge, hi⟩
  obtain ⟨k, hk, _⟩ := crossing_refined_node width hd hit.property (edge := other) rfl
  obtain ⟨j, s, hs, hj, _⟩ := PushPuzzle.Polygonal.Route.node_sample ((refinedDrawing width hd).route other) k
  by_contra hne
  have hef : edge ≠ other := fun h => hne (congrArg Fin.val h).symm
  rw [edgeFragment_eval] at he
  obtain ⟨u, v, _, hv, _⟩ := (refinedDrawing_isEmbedding width hd).edge_contacts edge other hef
    (edgeFragmentIndex width height hd hfit edge hhead piece i) j t s ht hs (he.trans (hj.trans hk).symm)
  exact crossing_ne_refined_endpoint width height hd hfit hit other v
    ((hj.trans hk).symm.trans (((refinedDrawing width hd).route other).at_eq_endpoint j hs v hv))

/-- A genuine source fragment contacts an emitted crossing only at its exact named boundary. -/
theorem edgeFragment_crossing_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (hit : {c // c ∈ crossings width d})
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i t = complexPoint (hit.val.location width d)) :
    ∃ side, (edgeFragment width height hd hfit edge hhead piece).AtEnd i t side ∧
      edgeStation width hd edge (if side then piece.succ else piece.castSucc) = .crossing hit := by
  have hc := crossing_mem_edgeStations width hd edge hit (fragment_crossing_edge width height hd hfit edge hhead piece i ht hit he)
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
  let cut : Fin ((edgeCrossings width d edge).length + 2) := ⟨k.val, by
    rw [← edgeStations_length width hd edge]
    exact k.isLt⟩
  have hcut : edgeStation width hd edge cut = .crossing hit := hk
  have he' : (edgeFragment width height hd hfit edge hhead piece).eval i t =
      complexPoint (stationPoint width d (edgeStation width hd edge cut)) := by rw [hcut]; exact he
  obtain ⟨side, hend, hs⟩ := edgeFragment_cut_contact width height hd hfit edge hhead piece cut i ht he'
  exact ⟨side, hend, hs ▸ hcut⟩

private theorem tip_native_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) :
    ∃ v ∈ G.vertices, complexPoint (stationPoint width d (.tip vertex)) = (refinedDrawing width hd).vertex v := by
  have hv : vertex.val < G.vertices.length := by rw [← hd.vertexCount]; exact vertex.isLt
  let v := G.vertices[vertex.val]
  have hi : G.vertices.idxOf v = vertex.val := hd.labelsNodup.idxOf_getElem vertex.val hv
  refine ⟨v, List.getElem_mem hv, ?_⟩
  change _ = (preparedDrawing width hd).vertex v
  rw [preparedDrawing_vertex]
  change complexPoint ((prepare width d).1.getD vertex (0, 0)) =
    complexPoint ((prepare width d).1.getD (G.vertices.idxOf v) (0, 0))
  rw [hi]

/-- A genuine source fragment contacts an original tooth tip only at its exact named boundary. -/
theorem edgeFragment_tip_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (vertex : Fin d.1.length)
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i t = complexPoint (stationPoint width d (.tip vertex))) :
    ∃ side, (edgeFragment width height hd hfit edge hhead piece).AtEnd i t side ∧
      edgeStation width hd edge (if side then piece.succ else piece.castSucc) = .tip vertex := by
  obtain ⟨v, hv, hp⟩ := tip_native_vertex width hd vertex
  have he' := he
  rw [edgeFragment_eval, hp] at he'
  obtain ⟨side, hend, _⟩ := (refinedDrawing_isEmbedding width hd).vertex_contacts edge
    (edgeFragmentIndex width height hd hfit edge hhead piece i) t ht v hv he'
  have hf := fragment_end_of_source width height hd hfit edge hhead piece i t ht side hend
  refine ⟨side, hf, ?_⟩
  apply stationPoint_injective width height hd hfit
  apply complexPoint_injective
  exact (edgeFragment_station_endpoint width height hd hfit edge hhead piece side).symm.trans
    (((edgeFragment width height hd hfit edge hhead piece).at_eq_endpoint i ht side hf).symm.trans he)

end PushPuzzle.PushS.Comb

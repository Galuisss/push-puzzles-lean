/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombToothOrder
public import PushS.PolygonalCutNodes
public import CslibFrontier.Computability.Complexity.Problems.Graph.OrthogonalDrawing.Polygonal
public import CslibFrontier.Computability.Complexity.Problems.Graph.PolygonalDrawing.CutTransport
import all PushS.CombPreprocess
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-! A genuine polygonal embedding of the same source graph at its actual prepared coordinates. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The actual strip preparation map, on the full complex plane as a real linear map. -/
@[expose] noncomputable def complexMap (width : ℕ) : ℂ →ₗ[ℝ] ℂ := by
  exact Complex.equivRealProdCLM.symm.toLinearMap.comp
    ((realLinearMap width).comp Complex.equivRealProdCLM.toLinearMap)

/-- The full-plane preparation retains exactly the emitted pair of real coordinates. -/
theorem equivRealProd_complexMap (width : ℕ) (z : ℂ) :
    Complex.equivRealProdCLM (complexMap width z) = realMap width (Complex.equivRealProdCLM z) := by
  exact Complex.equivRealProdCLM.apply_symm_apply _

/-- The same emitted integer map is the restriction of the actual full-plane linear map. -/
theorem complexMap_complexPoint (width : ℕ) (p : Point) :
    complexMap width (complexPoint p) = complexPoint (point width p) := by
  apply Complex.equivRealProdCLM.injective
  rw [equivRealProd_complexMap, equivRealProd_complexPoint, equivRealProd_complexPoint]
  exact (realPoint_point width p).symm

/-- The actual full-plane preparation is injective. -/
theorem complexMap_injective (width : ℕ) : Function.Injective (complexMap width) := by
  intro a b he
  apply Complex.equivRealProdCLM.injective
  apply realMap_injective width
  simpa only [equivRealProd_complexMap] using congrArg Complex.equivRealProdCLM he

/-- Map the original indexed route nodes by the actual strip preparation. -/
@[expose] noncomputable def preparedRoute (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) : Cslib.Polygonal.Route where
  bends := (hd.polygonalDrawing.route edge).bends
  point i := complexMap width ((hd.polygonalDrawing.route edge).point i)

/-- Segment indices and their complete real parameters are retained by the actual affine map. -/
theorem preparedRoute_eval (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (i : Fin (preparedRoute width hd edge).segments) (t : ℝ) :
    (preparedRoute width hd edge).eval i t = complexMap width ((hd.polygonalDrawing.route edge).eval i t) := by
  exact (AffineMap.apply_lineMap (complexMap width).toAffineMap _ _ _).symm

private theorem preparedRoute_endpoint (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) :
    (preparedRoute width hd edge).endpoint side = complexMap width ((hd.polygonalDrawing.route edge).endpoint side) := by
  cases side <;> rfl

private theorem preparedRoute_simple (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) : (preparedRoute width hd edge).IsSimple := by
  intro i j s t hs ht he
  rw [preparedRoute_eval, preparedRoute_eval] at he
  exact hd.isEmbedding_polygonalDrawing.simple edge i j s t hs ht ((complexMap_injective width) he)

private theorem preparedRoute_support (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    (preparedRoute width hd edge).support = complexMap width '' (hd.polygonalDrawing.route edge).support := by
  ext z
  constructor
  · intro hz
    obtain ⟨i, t, ht, rfl⟩ := ((preparedRoute width hd edge).mem_support_iff z).mp hz
    exact ⟨_, (hd.polygonalDrawing.route edge).at_mem_support i ht, (preparedRoute_eval width hd edge i t).symm⟩
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, t, ht, rfl⟩ := ((hd.polygonalDrawing.route edge).mem_support_iff w).mp hw
    exact ((preparedRoute width hd edge).mem_support_iff _).mpr ⟨i, t, ht, preparedRoute_eval width hd edge i t⟩

/-- Map the standard source polygonal drawing by the literal emitted strip preparation. -/
@[expose] noncomputable def preparedDrawing (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph.PolygonalDrawing G where
  vertex := fun v => complexMap width (hd.polygonalDrawing.vertex v)
  route := preparedRoute width hd
  endpoint_eq edge side := by
    exact (preparedRoute_endpoint width hd edge side).trans
      (congrArg (complexMap width) (hd.polygonalDrawing.endpoint_eq edge side))

/-- The actual prepared polygonal graph retains the original standard embedding validity. -/
theorem preparedDrawing_isEmbedding (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : (preparedDrawing width hd).IsEmbedding := by
  apply hd.isEmbedding_polygonalDrawing.of_route_map (complexMap_injective width) (fun _ => rfl)
    (preparedRoute_simple width hd)
  intro edge i
  refine ⟨i, 0, 1, le_rfl, zero_lt_one, le_rfl, ?_⟩
  intro t ht
  have hid : AffineMap.lineMap (0 : ℝ) 1 t = t := by simp [AffineMap.lineMap_apply_ring']
  constructor
  · rw [hid]
    exact preparedRoute_eval width hd edge i t
  · intro side
    rw [hid]
    rfl

/-- Each original vertex is placed at precisely its actual emitted prepared integer point. -/
theorem preparedDrawing_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (v : ℕ) :
    (preparedDrawing width hd).vertex v = complexPoint (Graph.drawingPosition G (prepare width d) v) := by
  change complexMap width (complexPoint (Graph.drawingPosition G d v)) = _
  rw [complexMap_complexPoint, drawingPosition_prepare]

private theorem support_toPolygonalRoute (r : Route) (hlen : 2 ≤ r.length) :
    Complex.equivRealProdCLM '' (toPolygonalRoute r hlen).support = support r := by
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    obtain ⟨i, t, ht, rfl⟩ := ((toPolygonalRoute r hlen).mem_support_iff w).mp hw
    exact eval_toPolygonalRoute_mem_support r hlen i ht
  · intro hz
    obtain ⟨ab, hab, hseg⟩ := mem_support_segment hlen hz
    obtain ⟨i, hi, hia, hib⟩ := List.mem_consecutivePairs_iff_exists_getElem.mp hab
    rw [Orthogonal.segment, _root_.segment_eq_image_lineMap] at hseg
    obtain ⟨t, ht, he⟩ := hseg
    let j : Fin (toPolygonalRoute r hlen).segments := ⟨i, by
      change i < r.length - 2 + 1
      omega⟩
    refine ⟨(toPolygonalRoute r hlen).eval j t, (toPolygonalRoute r hlen).at_mem_support j ht, ?_⟩
    have hmap := AffineMap.apply_lineMap Complex.equivRealProdCLM.toLinearMap.toAffineMap
      (complexPoint r[i]) (complexPoint r[i + 1]) t
    change Complex.equivRealProdCLM ((toPolygonalRoute r hlen).eval j t) =
      AffineMap.lineMap (Complex.equivRealProdCLM (complexPoint r[i]))
        (Complex.equivRealProdCLM (complexPoint r[i + 1])) t at hmap
    rw [equivRealProd_complexPoint, equivRealProd_complexPoint, hia, hib] at hmap
    exact hmap.trans he

private theorem source_polygonal_support {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (e : Fin G.edges.length) :
    Complex.equivRealProdCLM '' (hd.polygonalDrawing.route e).support = support (d.2.getD e []) := by
  have hlen : 2 ≤ (Graph.OrthogonalDrawing.sourceRoute G d e).reverse.length := by
    simpa only [List.length_reverse] using Graph.OrthogonalDrawing.sourceRoute_length_ge_two hd e.isLt
  change Complex.equivRealProdCLM '' (toPolygonalRoute _ hlen).support = _
  rw [support_toPolygonalRoute, support_reverse, Graph.OrthogonalDrawing.support_sourceRoute]

/-- Every source edge keeps exactly its full emitted prepared support, including all turns and cuts. -/
theorem preparedDrawing_route_support (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (e : Fin G.edges.length) :
    Complex.equivRealProdCLM '' ((preparedDrawing width hd).route e).support =
      support ((prepare width d).2.getD e []) := by
  have hsupport := preparedRoute_support width hd e
  change Complex.equivRealProdCLM '' (preparedRoute width hd e).support = _
  rw [hsupport, Set.image_image]
  have hm : (Complex.equivRealProdCLM ∘ complexMap width) = realMap width ∘ Complex.equivRealProdCLM :=
    funext (equivRealProd_complexMap width)
  change (Complex.equivRealProdCLM ∘ complexMap width) '' (hd.polygonalDrawing.route e).support = _
  rw [hm]
  change (fun z => realMap width (Complex.equivRealProdCLM z)) '' (hd.polygonalDrawing.route e).support = _
  rw [← Set.image_image (realMap width) Complex.equivRealProdCLM,
    source_polygonal_support, route_prepare, support_map_point]

/-- Each real emitted crossing lies on its exact original edge in the prepared polygonal embedding. -/
theorem crossing_mem_preparedDrawing (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {c : Crossing} (hc : c ∈ crossings width d)
    {edge : Fin G.edges.length} (he : edge.val = c.edge) :
    complexPoint (c.location width d) ∈ ((preparedDrawing width hd).route edge).support := by
  have hp := crossing_location_supported width hd hc
  rw [← he, ← preparedDrawing_route_support width hd edge] at hp
  obtain ⟨z, hz, heq⟩ := hp
  have hz' : z = complexPoint (c.location width d) :=
    Complex.equivRealProdCLM.injective (heq.trans (equivRealProd_complexPoint _).symm)
  exact hz' ▸ hz

/-- Every actual source edge remains open in the prepared embedding. -/
theorem preparedDrawing_route_open (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    ((preparedDrawing width hd).route edge).start ≠ ((preparedDrawing width hd).route edge).finish := by
  let D := preparedDrawing width hd
  have hleft := D.endpoint_eq edge false
  have hright := D.endpoint_eq edge true
  change (D.route edge).start = D.vertex (Graph.Dart.vertex (edge, false)) at hleft
  change (D.route edge).finish = D.vertex (Graph.Dart.vertex (edge, true)) at hright
  have hdecl := hd.endpointsDeclared G.edges[edge] (List.getElem_mem edge.isLt)
  have hne := hd.loopless G.edges[edge] (List.getElem_mem edge.isLt)
  rw [Graph.Dart.edge_eq_vertices edge] at hdecl hne
  intro he
  rw [hleft, hright] at he
  exact hne ((preparedDrawing_isEmbedding width hd).vertices_injective hdecl.1 hdecl.2 he)

private theorem complexPoint_re (p : Point) : (complexPoint p).re = (p.1 : ℝ) :=
  congrArg Prod.fst (equivRealProd_complexPoint p)

private theorem mapped_source_nonvertical (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (i : Fin (hd.polygonalDrawing.route edge).segments) :
    (complexMap width ((hd.polygonalDrawing.route edge).point i.castSucc)).re ≠
      (complexMap width ((hd.polygonalDrawing.route edge).point i.succ)).re := by
  let r := (Graph.OrthogonalDrawing.sourceRoute G d edge).reverse
  have hor : IsOrthogonal r := (isOrthogonal_reverse_iff _).mpr
    (Graph.OrthogonalDrawing.sourceRoute_regular hd edge.isLt).1
  have hi : i.val + 1 < r.length := by
    have hb := i.isLt
    change i.val < r.length - 2 + 1 at hb
    have hlen : 2 ≤ r.length := by
      simpa only [r, List.length_reverse] using Graph.OrthogonalDrawing.sourceRoute_length_ge_two hd edge.isLt
    omega
  change (complexMap width (complexPoint r[i.val])).re ≠ (complexMap width (complexPoint r[i.val + 1])).re
  rw [complexMap_complexPoint, complexMap_complexPoint, complexPoint_re, complexPoint_re]
  have hm : (point width r[i.val], point width r[i.val + 1]) ∈ (r.map (point width)).consecutivePairs := by
    rw [consecutivePairs_map_point]
    exact List.mem_map.mpr ⟨_, List.getElem_mem_consecutivePairs r i.val hi, rfl⟩
  have hshape := map_segment_slopes width hor _ hm
  have hproper := (hor _ (List.getElem_mem_consecutivePairs r i.val hi)).2
  intro he
  have hx : (point width r[i.val]).1 = (point width r[i.val + 1]).1 := by exact_mod_cast he
  apply hproper
  apply point_injective width
  apply Prod.ext hx
  rcases hshape with hy | hdiag
  · exact hy
  · change (point width r[i.val]).2 - (point width r[i.val]).1 =
      (point width r[i.val + 1]).2 - (point width r[i.val + 1]).1 at hdiag
    omega

/-- Every actual segment of the prepared polygonal drawing crosses tooth columns transversely. -/
theorem preparedDrawing_segment_nonvertical (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (i : Fin ((preparedDrawing width hd).route edge).segments) :
    (((preparedDrawing width hd).route edge).point i.castSucc).re ≠
      (((preparedDrawing width hd).route edge).point i.succ).re := by
  exact mapped_source_nonvertical width hd edge i

/-- The actual prepared tooth columns, as finite affine refinement levels. -/
@[expose] noncomputable def toothLevels (width : ℕ) (d : Graph.OrthogonalDrawing) : Finset ℝ :=
  ((prepare width d).1.map fun p => (p.1 : ℝ)).toFinset

/-- Refine the same prepared embedding at every actual tooth column. -/
@[expose] noncomputable def refinedDrawing (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph.PolygonalDrawing G :=
  (preparedDrawing width hd).mapAtCuts (S := toothLevels width d)
    (c := Complex.reCLM.toLinearMap.toAffineMap) (F := id) (fun _ _ _ _ _ => rfl)

/-- The actual all-tooth refinement is a genuine embedding of the unchanged indexed source graph. -/
theorem refinedDrawing_isEmbedding (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : (refinedDrawing width hd).IsEmbedding :=
  (preparedDrawing_isEmbedding width hd).mapAtCuts (fun _ _ _ _ _ => rfl) Function.injective_id

/-- Each marked encounter occupies one exact node index on its actual refined source edge. -/
theorem crossing_refined_node (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {c : Crossing} (hc : c ∈ crossings width d)
    {edge : Fin G.edges.length} (he : edge.val = c.edge) :
    ∃! k : Fin (((refinedDrawing width hd).route edge).bends + 2),
      ((refinedDrawing width hd).route edge).point k = complexPoint (c.location width d) := by
  have hmem : (prepare width d).1.getD c.vertex (0, 0) ∈ (prepare width d).1 := by
    have hi : c.vertex < (prepare width d).1.length := by
      simpa only [prepare, List.length_map] using crossing_vertex_lt width d hc
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hlevel : (complexPoint (c.location width d)).re ∈ toothLevels width d := by
    rw [complexPoint_re]
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  exact PushPuzzle.Polygonal.Route.existsUnique_node_mapAtCuts_of_level
    ((preparedDrawing_isEmbedding width hd).simple edge) (preparedDrawing_route_open width hd edge)
    (toothLevels width d) Complex.reCLM.toLinearMap.toAffineMap
    (preparedDrawing_segment_nonvertical width hd edge) (crossing_mem_preparedDrawing width hd hc he) hlevel

end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCrossingParameter

/-! Genuine indexed source-edge fragments between consecutive actual tooth encounters. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The exact refined route node of one actually emitted crossing of this original edge. -/
@[expose] noncomputable def edgeCrossingNode (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : {c // c ∈ edgeCrossings width d edge}) :
    Fin (((refinedDrawing width hd).route edge).bends + 2) := by
  have h := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hit.property)
  exact Classical.choose (crossing_refined_node width hd h.1 (of_decide_eq_true h.2).symm)

/-- The chosen node is the exact actual point of that same original crossing occurrence. -/
theorem edgeCrossingNode_point (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : {c // c ∈ edgeCrossings width d edge}) :
    ((refinedDrawing width hd).route edge).point (edgeCrossingNode width hd edge hit) =
      complexPoint (hit.val.location width d) := by
  unfold edgeCrossingNode
  have h := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hit.property)
  exact (Classical.choose_spec (crossing_refined_node width hd h.1 (of_decide_eq_true h.2).symm)).1

private theorem crossingNode_interior (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (hit : {c // c ∈ edgeCrossings width d edge}) :
    0 < edgeCrossingNode width hd edge hit ∧ edgeCrossingNode width hd edge hit <
      Fin.last (((refinedDrawing width hd).route edge).bends + 1) := by
  obtain ⟨hc, he⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hit.property)
  obtain ⟨i, t, _, ht, hval⟩ := crossing_prepared_parameter width hd edge hhead hc (of_decide_eq_true he).symm
  exact PushPuzzle.Polygonal.Route.mapAtCuts_node_interior ((preparedDrawing_isEmbedding width hd).simple edge)
    (preparedDrawing_route_open width hd edge) (toothLevels width d) Complex.reCLM.toLinearMap.toAffineMap
    (edgeCrossingNode width hd edge hit) i t ht ((edgeCrossingNode_point width hd edge hit).trans hval.symm)

/-- The complete actual cut-node sequence of an original edge, retaining both original ends. -/
@[expose] noncomputable def edgeCutNodes (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    List (Fin (((refinedDrawing width hd).route edge).bends + 2)) :=
  0 :: (edgeCrossings width d edge).attach.map (edgeCrossingNode width hd edge) ++
    [Fin.last (((refinedDrawing width hd).route edge).bends + 1)]

/-- The actual endpoints add exactly two nodes to the original crossing list. -/
theorem edgeCutNodes_length (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    (edgeCutNodes width hd edge).length = (edgeCrossings width d edge).length + 2 := by
  simp only [edgeCutNodes, List.length_cons, List.length_append, List.length_map, List.length_attach,
    List.length_nil]

/-- The complete emitted cut-node list follows strictly increasing actual route indices. -/
theorem edgeCutNodes_strict (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    (edgeCutNodes width hd edge).Pairwise (· < ·) := by
  let hits := edgeCrossings width d edge
  have hp := edgeCrossings_refined_nodes_order width height hd hfit edge hhead
  have hattach : hits.attach.map Subtype.val = hits := by simp
  dsimp only [hits] at hattach
  rw [← hattach, List.pairwise_map] at hp
  have hmiddle : (hits.attach.map (edgeCrossingNode width hd edge)).Pairwise (· < ·) := by
    rw [List.pairwise_map]
    exact hp.imp (fun h => h _ _ (edgeCrossingNode_point width hd edge _) (edgeCrossingNode_point width hd edge _))
  have hbound (k : Fin (((refinedDrawing width hd).route edge).bends + 2))
      (hk : k ∈ hits.attach.map (edgeCrossingNode width hd edge)) :
      0 < k ∧ k < Fin.last (((refinedDrawing width hd).route edge).bends + 1) := by
    obtain ⟨hit, _, rfl⟩ := List.mem_map.mp hk
    exact crossingNode_interior width hd edge hhead hit
  apply List.pairwise_cons.mpr
  constructor
  · intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact (hbound _ hk).1
    · simp only [List.mem_singleton] at hk
      subst k
      change 0 < ((refinedDrawing width hd).route edge).bends + 1
      omega
  · apply List.pairwise_append.mpr
    exact ⟨hmiddle, by simp, fun a ha b hb => by
      simp only [List.mem_singleton] at hb
      subst b
      exact (hbound a ha).2⟩

/-- Select one actual cut node by its position in the complete original-edge cut list. -/
@[expose] noncomputable def edgeCutNode (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (index : Fin ((edgeCrossings width d edge).length + 2)) :
    Fin (((refinedDrawing width hd).route edge).bends + 2) :=
  (edgeCutNodes width hd edge).get ⟨index.val, by rw [edgeCutNodes_length]; exact index.isLt⟩

/-- The selected source-edge cut indices form a strictly increasing finite map. -/
theorem edgeCutNode_strictMono (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    StrictMono (edgeCutNode width hd edge) := by
  intro i j hij
  exact List.pairwise_iff_get.mp (edgeCutNodes_strict width height hd hfit edge hhead) _ _ hij

/-- The genuine polygonal route between consecutive actual source-edge encounters. -/
@[expose] noncomputable def edgeFragment (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1)) : Cslib.Polygonal.Route :=
  (PushPuzzle.Polygonal.Route.subroute ((refinedDrawing width hd).route edge)) (edgeCutNode width hd edge piece.castSucc)
    (edgeCutNode width hd edge piece.succ)
    (edgeCutNode_strictMono width height hd hfit edge hhead Fin.castSucc_lt_succ)

/-- The actual source segment index corresponding to one retained fragment segment. -/
@[expose] noncomputable def edgeFragmentIndex (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) :
    Fin ((refinedDrawing width hd).route edge).segments :=
  (PushPuzzle.Polygonal.Route.subrouteIndex ((refinedDrawing width hd).route edge)) (edgeCutNode width hd edge piece.castSucc)
    (edgeCutNode width hd edge piece.succ)
    (edgeCutNode_strictMono width height hd hfit edge hhead Fin.castSucc_lt_succ) i

/-- Every real parameter of a fragment is retained at its actual original refined segment. -/
theorem edgeFragment_eval (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) (t : ℝ) :
    (edgeFragment width height hd hfit edge hhead piece).eval i t =
      ((refinedDrawing width hd).route edge).eval (edgeFragmentIndex width height hd hfit edge hhead piece i) t :=
  PushPuzzle.Polygonal.Route.eval_subroute _ _ _ _ _ _

private theorem fragment_end_of_source (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) (t : ℝ) (ht : t ∈ Set.Icc 0 1) (side : Bool)
    (he : ((refinedDrawing width hd).route edge).AtEnd (edgeFragmentIndex width height hd hfit edge hhead piece i) t side) :
    (edgeFragment width height hd hfit edge hhead piece).AtEnd i t side :=
  PushPuzzle.Polygonal.Route.atEnd_subroute_of_source _ _ _ _ _ _ ht side he

/-- Each fragment retains precisely the two actual boundary points of its original-edge interval. -/
theorem edgeFragment_endpoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    (edgeFragment width height hd hfit edge hhead piece).endpoint side =
      ((refinedDrawing width hd).route edge).point
        (edgeCutNode width hd edge (if side then piece.succ else piece.castSucc)) := by
  unfold edgeFragment
  rw [PushPuzzle.Polygonal.Route.endpoint_subroute]
  cases side <;> rfl

/-- Each actual fragment is a simple polygonal route with all its real segment parameters retained. -/
theorem edgeFragment_simple (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1)) :
    (edgeFragment width height hd hfit edge hhead piece).IsSimple := by
  exact (PushPuzzle.Polygonal.Route.IsSimple.subroute ((refinedDrawing_isEmbedding width hd).simple edge)) _ _ _

/-- Every point of each actual fragment remains on the same original indexed source route. -/
theorem edgeFragment_support_subset (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1)) :
    (edgeFragment width height hd hfit edge hhead piece).support ⊆ ((refinedDrawing width hd).route edge).support := by
  exact PushPuzzle.Polygonal.Route.support_subroute_subset _ _ _ _

private theorem refined_route_open (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    ((refinedDrawing width hd).route edge).start ≠ ((refinedDrawing width hd).route edge).finish := by
  have hs := Cslib.Polygonal.Route.endpoint_mapAtCuts (S := toothLevels width d)
    (c := Complex.reCLM.toLinearMap.toAffineMap) (F := id) (fun _ _ _ _ _ => rfl)
    ((preparedDrawing width hd).route edge) false
  have ht := Cslib.Polygonal.Route.endpoint_mapAtCuts (S := toothLevels width d)
    (c := Complex.reCLM.toLinearMap.toAffineMap) (F := id) (fun _ _ _ _ _ => rfl)
    ((preparedDrawing width hd).route edge) true
  change ((refinedDrawing width hd).route edge).start = ((preparedDrawing width hd).route edge).start at hs
  change ((refinedDrawing width hd).route edge).finish = ((preparedDrawing width hd).route edge).finish at ht
  simpa only [hs, ht] using preparedDrawing_route_open width hd edge

/-- Distinct ordered fragments of one real original edge contact only as consecutive pieces. -/
theorem edgeFragments_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (left right : Fin ((edgeCrossings width d edge).length + 1)) (hlr : left < right)
    (i : Fin (edgeFragment width height hd hfit edge hhead left).segments)
    (j : Fin (edgeFragment width height hd hfit edge hhead right).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit edge hhead left).eval i s =
      (edgeFragment width height hd hfit edge hhead right).eval j t) :
    left.val + 1 = right.val ∧ (edgeFragment width height hd hfit edge hhead left).AtEnd i s true ∧
      (edgeFragment width height hd hfit edge hhead right).AtEnd j t false := by
  have hm := edgeCutNode_strictMono width height hd hfit edge hhead
  have hbc : edgeCutNode width hd edge left.succ ≤ edgeCutNode width hd edge right.castSucc := by
    apply hm.monotone
    change left.val + 1 ≤ right.val
    exact hlr
  have h := (PushPuzzle.Polygonal.Route.IsSimple.subroute_contact ((refinedDrawing_isEmbedding width hd).simple edge)) (refined_route_open width hd edge)
    (edgeCutNode width hd edge left.castSucc) (edgeCutNode width hd edge left.succ)
    (edgeCutNode width hd edge right.castSucc) (edgeCutNode width hd edge right.succ)
    (hm Fin.castSucc_lt_succ) (hm Fin.castSucc_lt_succ) hbc i j s t hs ht he
  refine ⟨?_, h.2⟩
  exact congrArg Fin.val (hm.injective h.1)

/-- Fragments from different original edges meet only at their common original endpoint. -/
theorem edgeFragments_contact_distinct (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (left right : Fin G.edges.length) (hlr : left ≠ right)
    (hleft : (d.2.getD left []).head? = some (Graph.drawingPosition G d G.edges[left].1))
    (hright : (d.2.getD right []).head? = some (Graph.drawingPosition G d G.edges[right].1))
    (a : Fin ((edgeCrossings width d left).length + 1)) (b : Fin ((edgeCrossings width d right).length + 1))
    (i : Fin (edgeFragment width height hd hfit left hleft a).segments)
    (j : Fin (edgeFragment width height hd hfit right hright b).segments)
    (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit left hleft a).eval i s =
      (edgeFragment width height hd hfit right hright b).eval j t) :
    ∃ u v, (edgeFragment width height hd hfit left hleft a).AtEnd i s u ∧
      (edgeFragment width height hd hfit right hright b).AtEnd j t v ∧
      Graph.Dart.vertex (left, u) = Graph.Dart.vertex (right, v) := by
  rw [edgeFragment_eval, edgeFragment_eval] at he
  obtain ⟨u, v, hu, hv, heq⟩ := (refinedDrawing_isEmbedding width hd).edge_contacts left right hlr
    (edgeFragmentIndex width height hd hfit left hleft a i) (edgeFragmentIndex width height hd hfit right hright b j)
    s t hs ht he
  exact ⟨u, v, fragment_end_of_source width height hd hfit left hleft a i s hs u hu,
    fragment_end_of_source width height hd hfit right hright b j t ht v hv, heq⟩

end PushPuzzle.PushS.Comb

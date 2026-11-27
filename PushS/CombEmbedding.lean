/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPieceContacts
import all PushS.CombPieceContacts

/-! A standard polygonal embedding constructed from the actual raw source and actual comb tree. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- The actual indexed augmented graph on the literal numbered source-comb station array. -/
@[expose] def augmentedGraph (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph :=
  ⟨List.range (stations width d).length,
    (pieces width G d).map (fun piece =>
      (stationNumber width d (piece.station width hd false), stationNumber width d (piece.station width hd true)))⟩

/-- The genuine geometric piece stored at one actual augmented edge-array index. -/
@[expose] def augmentedPiece (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin (augmentedGraph width hd).edges.length) : Piece width G d :=
  (pieces width G d).get ⟨edge.val, by simpa only [augmentedGraph, List.length_map] using edge.isLt⟩

/-- Every actual augmented dart carries precisely the stored number of its geometric end station. -/
theorem augmented_dart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin (augmentedGraph width hd).edges.length) (side : Bool) :
    Graph.Dart.vertex (edge, side) = stationNumber width d ((augmentedPiece width hd edge).station width hd side) := by
  change (if side then ((augmentedGraph width hd).edges.getD edge (0, 0)).2
    else ((augmentedGraph width hd).edges.getD edge (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ edge.isLt]
  simp only [augmentedGraph, List.getElem_map]
  cases side <;> rfl

/-- The actual augmentation declares both ends of every indexed source or comb-tree edge. -/
theorem augmented_endpoints_declared (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) :
    ∀ edge ∈ (augmentedGraph width hd).edges, edge.1 ∈ (augmentedGraph width hd).vertices ∧
      edge.2 ∈ (augmentedGraph width hd).vertices := by
  intro edge he
  obtain ⟨piece, _, rfl⟩ := List.mem_map.mp he
  exact ⟨List.mem_range.mpr (stationNumber_lt width d _), List.mem_range.mpr (stationNumber_lt width d _)⟩

/-- Every endpoint occurrence of the actual augmented graph is a declared station number. -/
theorem augmented_incidence_declared (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) :
    ∀ vertex ∈ (augmentedGraph width hd).incidenceVertices, vertex ∈ (augmentedGraph width hd).vertices := by
  intro vertex hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  have hdecl := augmented_endpoints_declared width hd edge he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl
  · exact hdecl.1
  · exact hdecl.2

private theorem augmentedPiece_injective (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Function.Injective (augmentedPiece width hd) := by
  intro a b he
  have h := (pieces_nodup width G d).get_inj_iff.mp he
  have hv : a.val = b.val := congrArg (fun k : Fin (pieces width G d).length => k.val) h
  exact Fin.ext hv

private theorem station_of_number (width : ℕ) (d : Graph.OrthogonalDrawing) {label : ℕ}
    (hl : label ∈ List.range (stations width d).length) :
    ∃ station : Station width d, stationNumber width d station = label := by
  have hi := List.mem_range.mp hl
  exact ⟨(stations width d).get ⟨label, hi⟩, (stations_nodup width d).idxOf_getElem label hi⟩

/-- Real source fragments, spine pieces and tooth pieces form one standard polygonal drawing. -/
@[expose] noncomputable def augmentedDrawing (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (hhead : ∀ edge : Fin G.edges.length,
      (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    Graph.PolygonalDrawing (augmentedGraph width hd) where
  vertex label := complexPoint (stationPosition width d label)
  route edge := (augmentedPiece width hd edge).route width height hd hfit hhead
  endpoint_eq edge side := by
    rw [augmented_dart_vertex, stationPosition_number]
    exact (augmentedPiece width hd edge).route_endpoint width height hd hfit hhead side

/-- The supplied actual source drawing constructs a genuine embedding of the whole augmented comb. -/
theorem augmentedDrawing_isEmbedding (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (hhead : ∀ edge : Fin G.edges.length,
      (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    (augmentedDrawing width height hd hfit hhead).IsEmbedding := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a ha b hb he
    have ha' := List.mem_range.mp ha
    have hb' := List.mem_range.mp hb
    apply stationPosition_injective width height hd hfit (by simpa only [stationPositions, List.length_map] using ha')
      (by simpa only [stationPositions, List.length_map] using hb')
    exact complexPoint_injective he
  · intro edge
    exact (augmentedPiece width hd edge).simple width height hd hfit hhead
  · intro edge i t ht label hl he
    obtain ⟨station, hs⟩ := station_of_number width d hl
    change _ = complexPoint (stationPosition width d label) at he
    rw [← hs, stationPosition_number] at he
    obtain ⟨side, hend, hn⟩ := (augmentedPiece width hd edge).station_contact width height hd hfit hhead i ht station he
    refine ⟨side, hend, ?_⟩
    rw [augmented_dart_vertex, hn, hs]
  · intro edge other hne i j s t hs ht he
    have hp : augmentedPiece width hd edge ≠ augmentedPiece width hd other :=
      fun h => hne (augmentedPiece_injective width hd h)
    obtain ⟨a, b, ha, hb, hn⟩ := (augmentedPiece width hd edge).edge_contacts width height hd hfit hhead
      (augmentedPiece width hd other) hp i j hs ht he
    refine ⟨a, b, ha, hb, ?_⟩
    rw [augmented_dart_vertex, augmented_dart_vertex, hn]

end PushPuzzle.PushS.Comb

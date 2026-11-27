/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombGenus
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.EdgeContractionGenus
import all PushS.CombGenus

/-! Reverse only auxiliary comb-tree ends so the actual last-edge contraction order is leaf-to-root. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- Source-fragment directions are retained; only the auxiliary comb-tree edges are reversed. -/
@[expose] def Piece.treeFlip {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} : Piece width G d → Bool
  | .source _ _ => false
  | .spine _ => true
  | .tooth _ _ => true

/-- The actual station at a leaf-to-root oriented edge end. -/
@[expose] def Piece.rootStation (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) : Station width d :=
  piece.station width hd (side ^^ piece.treeFlip)

/-- The same indexed augmented graph, with the auxiliary teeth directed down and spine left. -/
@[expose] def rootedGraph (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph :=
  ⟨List.range (stations width d).length, (pieces width G d).map (fun piece =>
    (stationNumber width d (piece.rootStation width hd false), stationNumber width d (piece.rootStation width hd true)))⟩

/-- The actual geometric piece at the unchanged edge-array position. -/
@[expose] def rootedPiece (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin (rootedGraph width hd).edges.length) : Piece width G d :=
  (pieces width G d).get ⟨edge.val, by simpa only [rootedGraph, List.length_map] using edge.isLt⟩

/-- Each reoriented actual dart has precisely its own named station number. -/
theorem rooted_dart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin (rootedGraph width hd).edges.length) (side : Bool) :
    Graph.Dart.vertex (edge, side) = stationNumber width d ((rootedPiece width hd edge).rootStation width hd side) := by
  change (if side then ((rootedGraph width hd).edges.getD edge (0, 0)).2
    else ((rootedGraph width hd).edges.getD edge (0, 0)).1) = _
  rw [List.getD_eq_getElem _ _ edge.isLt]
  simp only [rootedGraph, List.getElem_map]
  cases side <;> rfl

/-- Actual edge indices and source tags are retained, with only the auxiliary tree end tags flipped. -/
@[expose] def rootedDartEquiv (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph.Dart (rootedGraph width hd) ≃ Graph.Dart (augmentedGraph width hd) where
  toFun dart := (⟨dart.1.val, by simpa only [rootedGraph, augmentedGraph, List.length_map] using dart.1.isLt⟩,
    dart.2 ^^ (rootedPiece width hd dart.1).treeFlip)
  invFun dart := (⟨dart.1.val, by simpa only [rootedGraph, augmentedGraph, List.length_map] using dart.1.isLt⟩,
    dart.2 ^^ (augmentedPiece width hd dart.1).treeFlip)
  left_inv dart := by
    apply Prod.ext
    · rfl
    · change ((dart.2 ^^ (rootedPiece width hd dart.1).treeFlip) ^^ (rootedPiece width hd dart.1).treeFlip) = dart.2
      simp
  right_inv dart := by
    apply Prod.ext
    · rfl
    · change ((dart.2 ^^ (augmentedPiece width hd dart.1).treeFlip) ^^ (augmentedPiece width hd dart.1).treeFlip) = dart.2
      simp

/-- The explicit end-tag equivalence retains each actual named geometric vertex. -/
theorem rootedDartEquiv_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (rootedGraph width hd)) :
    (rootedDartEquiv width hd dart).vertex = dart.vertex := by
  rw [augmented_dart_vertex, rooted_dart_vertex]
  rfl

/-- The explicit end-tag equivalence preserves the actual reversal of each listed edge. -/
theorem rootedDartEquiv_reverse (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (rootedGraph width hd)) :
    rootedDartEquiv width hd dart.reverse = (rootedDartEquiv width hd dart).reverse := by
  apply Prod.ext
  · rfl
  · change (!dart.2 ^^ (rootedPiece width hd dart.1).treeFlip) = !(dart.2 ^^ (rootedPiece width hd dart.1).treeFlip)
    cases dart.2 <;> cases (rootedPiece width hd dart.1).treeFlip <;> rfl

private theorem rooted_incidence_declared (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) :
    ∀ vertex ∈ (rootedGraph width hd).incidenceVertices, vertex ∈ (rootedGraph width hd).vertices := by
  intro vertex hv
  obtain ⟨edge, he, hv⟩ := List.mem_flatMap.mp hv
  obtain ⟨piece, _, rfl⟩ := List.mem_map.mp he
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl <;> exact List.mem_range.mpr (stationNumber_lt width d _)

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- Transport the actual geometric rotation through the explicit auxiliary tree-end flips. -/
@[expose] noncomputable def rootedRotation : Graph.RotationSystem (rootedGraph width hd) :=
  (augmentedRotation width height hd hfit hhead).transport (rootedDartEquiv width hd).symm (by
    intro a b
    rw [← rootedDartEquiv_vertex width hd ((rootedDartEquiv width hd).symm a),
      ← rootedDartEquiv_vertex width hd ((rootedDartEquiv width hd).symm b)]
    simp only [Equiv.apply_symm_apply])

/-- Reorienting only auxiliary tree edges retains the actual augmented numerical genus zero. -/
theorem rootedRotation_numericalGenusZero :
    (rootedRotation width height hd hfit hhead).NumericalGenusZero := by
  apply (augmentedRotation width height hd hfit hhead).numericalGenusZero_transport
    (rootedDartEquiv width hd).symm _ ?_ (augmented_incidence_declared width hd) (rooted_incidence_declared width hd)
    (augmentedRotation_numericalGenusZero width height hd hfit hhead)
  · intro dart
    apply (rootedDartEquiv width hd).injective
    rw [rootedDartEquiv_reverse, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

end Geometry
end PushPuzzle.PushS.Comb

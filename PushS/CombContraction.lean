/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTreeEdgeWord
public import PushS.RootedTreeContraction
public import PushS.RotationContractionWords
public import CslibFrontier.Computability.Complexity.Problems.Graph.ClosedPassages.Loop
import all PushS.CombEmbedding
import all PushS.CombRootedOrientation

/-! Actual standard contraction of the original native comb tree retains the indexed source fragments. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Graph.RootedTreeGrowth

/-- The original indexed source-fragment prefix on the same complete native station declarations. -/
@[expose] def sourceBase (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Graph :=
  ⟨(rootedGraph width hd).vertices,
    ((List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge))).map
      (fun piece => (stationNumber width d (piece.rootStation width hd false), stationNumber width d (piece.rootStation width hd true)))⟩

/-- The actual native rooted graph is literally the original source prefix with its genuine tree word appended. -/
theorem rootedGraph_eq_source_tree (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) :
    rootedGraph width hd = graph (sourceBase width hd) (treeEdges width d hv) := by
  apply Graph.ext
  · rfl
  · exact rooted_edges_eq_tree_word width hd hv

/-- The exact indexed source graph after removing the actual native comb-tree edges. -/
@[expose] def contractedGraph (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) : Graph :=
  contractedBase (sourceBase width hd) (treeEdges width d hv)

/-- The complete actual tree contraction retains exactly the original source-fragment edge count. -/
theorem contractedGraph_edgeCount (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) :
    (contractedGraph width hd hv).edges.length = (sourceBase width hd).edges.length :=
  contractedBase_edges_length _ _

/-- The actual full comb-tree contraction sends every retained source edge end to the original first foot. -/
theorem contractedGraph_eq_root (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (hv : 0 < d.1.length) :
    contractedGraph width hd hv =
      ⟨(sourceBase width hd).vertices.map (fun _ => treeRoot width d hv),
        (sourceBase width hd).edges.map (fun _ => (treeRoot width d hv, treeRoot width d hv))⟩ := by
  apply (treeEdges_growth width height hd hfit hv).contractedBase_eq_root
  · intro label hl
    obtain ⟨station, hs⟩ := station_of_number width d hl
    rw [← hs]
    exact station_mem_tree_nodes width d hv station
  · intro edge he
    obtain ⟨piece, _, rfl⟩ := List.mem_map.mp he
    exact ⟨station_mem_tree_nodes width d hv _, station_mem_tree_nodes width d hv _⟩

/-- Every retained original fragment is an actual listed loop after contracting the genuine comb tree. -/
theorem contractedGraph_loops (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (hv : 0 < d.1.length)
    (edge : Fin (contractedGraph width hd hv).edges.length) :
    Graph.Dart.vertex (edge, false) = Graph.Dart.vertex (edge, true) := by
  have he : (contractedGraph width hd hv).edges[edge] ∈ (contractedGraph width hd hv).edges := List.getElem_mem edge.isLt
  generalize hp : (contractedGraph width hd hv).edges[edge] = pair at he
  rw [contractedGraph_eq_root width height hd hfit hv] at he
  obtain ⟨old, _, heq⟩ := List.mem_map.mp he
  have hpair : (contractedGraph width hd hv).edges[edge] = (treeRoot width d hv, treeRoot width d hv) := hp.trans heq.symm
  rw [Graph.Dart.edge_eq_vertices edge] at hpair
  exact (congrArg Prod.fst hpair).trans (congrArg Prod.snd hpair).symm

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) (hv : 0 < d.1.length)

/-- Reverse actual growth order constructs a standard contraction trace from the original native geometric rotation. -/
theorem exists_actual_contraction : ∃ r : Graph.RotationSystem (contractedGraph width hd hv),
    Graph.RotationSystem.ContractionTrace (rootedRotation width height hd hfit hhead) r := by
  let first := Graph.RotationSystem.castGraph (rootedGraph_eq_source_tree width hd hv)
    (rootedRotation width height hd hfit hhead)
  obtain ⟨r, hr⟩ := (treeEdges_growth width height hd hfit hv).exists_contraction (sourceBase width hd) first
  exact ⟨r, (Graph.RotationSystem.ContractionTrace.cast (rootedGraph_eq_source_tree width hd hv)
    (rootedRotation width height hd hfit hhead)).trans hr⟩

/-- The rotation produced by genuine standard contractions of the actual native comb tree. -/
@[expose] noncomputable def contractedRotation : Graph.RotationSystem (contractedGraph width hd hv) :=
  Classical.choose (exists_actual_contraction width height hd hfit hhead hv)

/-- The retained rotation comes from the complete actual source through a real standard contraction trace. -/
theorem contractedRotation_trace : Graph.RotationSystem.ContractionTrace
    (rootedRotation width height hd hfit hhead) (contractedRotation width height hd hfit hhead hv) :=
  Classical.choose_spec (exists_actual_contraction width height hd hfit hhead hv)

/-- The actual contracted source-fragment loops retain numerical genus zero. -/
theorem contractedRotation_numericalGenusZero :
    (contractedRotation width height hd hfit hhead hv).NumericalGenusZero :=
  ((contractedRotation_trace width height hd hfit hhead hv).preserves (rooted_incidence_declared width hd)
    (rootedRotation_numericalGenusZero width height hd hfit hhead)).2

/-- Distinct actual retained source-fragment loops do not alternate in the actual contracted rotation. -/
theorem contractedRotation_not_alternates (left right : Fin (contractedGraph width hd hv).edges.length)
    (hne : left ≠ right) :
    ¬(contractedRotation width height hd hfit hhead hv).Alternates (left, false) (left, true) (right, false) (right, true) := by
  have hdecl := ((contractedRotation_trace width height hd hfit hhead hv).preserves (rooted_incidence_declared width hd)
    (rootedRotation_numericalGenusZero width height hd hfit hhead)).1
  exact (contractedRotation width height hd hfit hhead hv).not_alternates_loops hdecl
    (contractedRotation_numericalGenusZero width height hd hfit hhead hv) left right hne
    (contractedGraph_loops width height hd hfit hv left) (contractedGraph_loops width height hd hfit hv right)

/-- The actual final rotation retains precisely the original directed source-prefix word after deleting all tree darts. -/
theorem contractedRotation_word (word : List (Graph.Dart (rootedGraph width hd))) (hn : word.Nodup)
    (htour : (PushPuzzle.Graph.RotationSystem.treeTour (rootedRotation width height hd hfit hhead)) (sourceBase width hd).edges.length = word.formPerm) :
    ∃ retained : List (Graph.Dart (contractedGraph width hd hv)), retained.Nodup ∧
      (contractedRotation width height hd hfit hhead hv).rotate = retained.formPerm ∧
      retained.map Graph.Dart.edgeCoordinates =
        (word.map Graph.Dart.edgeCoordinates).filter (fun coordinate => decide (coordinate.1 < (sourceBase width hd).edges.length)) := by
  have hlength := contractedGraph_edgeCount width hd hv
  obtain ⟨retained, hretained, hTour, hword⟩ := (contractedRotation_trace width height hd hfit hhead hv).preserves_word
    (sourceBase width hd).edges.length (by rw [hlength]) word hn htour
  refine ⟨retained, hretained, ?_, ?_⟩
  · rw [Graph.RotationSystem.treeTour_all_source _ _ (by rw [hlength])] at hTour
    exact hTour
  · simpa only [hlength] using hword

end Geometry
end PushPuzzle.PushS.Comb

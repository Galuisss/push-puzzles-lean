/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTreeGrowth

/-! Actual rooted piece endpoints recover exactly the literal fresh-child tree edge word. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Graph.RootedTreeGrowth

private theorem toothStation_zero (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    toothStation width d vertex 0 = .foot vertex := by
  simp only [toothStation, toothStations, List.get_eq_getElem, List.cons_append, Fin.val_zero, List.getElem_cons_zero]

private theorem tooth_children (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    List.ofFn (fun piece : Fin ((toothCrossings width d vertex).length + 1) =>
      stationNumber width d (toothStation width d vertex piece.succ)) =
        (toothStations width d vertex).tail.map (stationNumber width d) := by
  have h := congrArg List.tail (toothStations_ofFn width d vertex)
  rw [List.ofFn_succ] at h
  simp only [List.tail_cons] at h
  rw [← h, List.map_ofFn]
  rfl

/-- The actual bottom-to-top tooth piece array is exactly its literal child-to-parent path word. -/
theorem tooth_piece_word (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) :
    (List.ofFn (Piece.tooth (width := width) (G := G) vertex)).map (fun piece =>
      (stationNumber width d (piece.rootStation width hd false), stationNumber width d (piece.rootStation width hd true))) =
      pathEdges (stationNumber width d (.foot vertex)) ((toothStations width d vertex).tail.map (stationNumber width d)) := by
  simp only [List.map_ofFn]
  change List.ofFn (fun piece : Fin ((toothCrossings width d vertex).length + 1) =>
    (stationNumber width d (toothStation width d vertex piece.succ),
      stationNumber width d (toothStation width d vertex piece.castSucc))) = _
  rw [← pathEdges_ofFn (fun index => stationNumber width d (toothStation width d vertex index)),
    toothStation_zero, tooth_children]

/-- The actual left-to-right spine piece array is its exact consecutive child-to-parent path word. -/
theorem spine_piece_word (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) :
    (List.ofFn (Piece.spine (width := width) (G := G) (d := d))).map (fun piece =>
      (stationNumber width d (piece.rootStation width hd false), stationNumber width d (piece.rootStation width hd true))) =
      pathEdges (treeRoot width d hv) (spineLabels width d).tail := by
  have h := pathEdges_tail_ofFn hv (fun rank => stationNumber width d (.foot (spineVertex width d rank)))
  rw [List.map_ofFn]
  change List.ofFn (fun i : Fin (d.1.length - 1) =>
    (stationNumber width d (.foot (spineRight width d i)), stationNumber width d (.foot (spineLeft width d i)))) = _
  simpa only [spineLabels, spineStations, List.map_ofFn, Function.comp_def, treeRoot, spineLeft, spineRight] using h.symm

/-- The rooted actual augmented edge array is the original source-fragment word followed by the actual growing comb tree. -/
theorem rooted_edges_eq_tree_word (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) :
    (rootedGraph width hd).edges =
      ((List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge))).map
        (fun piece => (stationNumber width d (piece.rootStation width hd false), stationNumber width d (piece.rootStation width hd true))) ++
      treeEdges width d hv := by
  simp only [rootedGraph, pieces, List.map_append, List.map_flatMap, treeEdges, toothBranches,
    List.flatMap_map, List.append_assoc]
  rw [spine_piece_word width hd hv]
  congr 2
  apply congrArg (fun f => (List.finRange d.1.length).flatMap f)
  funext vertex
  exact tooth_piece_word width hd vertex

end PushPuzzle.PushS.Comb

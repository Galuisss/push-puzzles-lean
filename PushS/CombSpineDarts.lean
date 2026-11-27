/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombToothDarts
import all PushS.CombToothOrder
import all PushS.CombDarts

/-! Canonical actual left and right spine darts at each original numbered native foot. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The literal original source vertex's position in the actual sorted foot array. -/
@[expose] def spineRank (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) : Fin d.1.length :=
  ⟨vertexRank width d vertex, by exact vertexRank_lt width d vertex.isLt⟩

/-- Re-reading the canonical source rank returns exactly that original native vertex. -/
theorem spineVertex_spineRank (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    spineVertex width d (spineRank width d vertex) = vertex := by
  obtain ⟨index, hrank, hvertex, _⟩ := ordered_site width d vertex.isLt
  apply Fin.ext
  change ((vertexOrder width d).get ⟨vertexRank width d vertex, by
    rw [vertexOrder_length]
    exact vertexRank_lt width d vertex.isLt⟩).2 = vertex.val
  have hi : (⟨vertexRank width d vertex, by rw [vertexOrder_length]; exact vertexRank_lt width d vertex.isLt⟩ :
      Fin (vertexOrder width d).length) = index := Fin.ext hrank.symm
  rw [hi]
  exact hvertex

/-- Reading the source identity at a spine position retains that exact original array rank. -/
theorem spineRank_spineVertex (width : ℕ) (d : Graph.OrthogonalDrawing) (rank : Fin d.1.length) :
    spineRank width d (spineVertex width d rank) = rank := by
  have hperm := (vertexOrder_perm width d).map Prod.snd
  have hn := hperm.nodup_iff.mpr (List.nodup_zipIdx_map_snd (prepare width d).1)
  have hi : rank.val < ((vertexOrder width d).map Prod.snd).length := by
    rw [List.length_map, vertexOrder_length]
    exact rank.isLt
  have he := hn.idxOf_getElem rank.val hi
  apply Fin.ext
  simpa only [spineRank, vertexRank, spineVertex, List.getElem_map, List.get_eq_getElem] using he

/-- The actual left endpoint of a spine piece retains that piece's own array rank. -/
theorem spineLeft_rank (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1)) :
    vertexRank width d (spineLeft width d piece) = piece.val :=
  congrArg Fin.val (spineRank_spineVertex width d ⟨piece.val, by have := piece.isLt; omega⟩)

/-- The actual right endpoint of a spine piece retains its next array rank. -/
theorem spineRight_rank (width : ℕ) (d : Graph.OrthogonalDrawing) (piece : Fin (d.1.length - 1)) :
    vertexRank width d (spineRight width d piece) = piece.val + 1 :=
  congrArg Fin.val (spineRank_spineVertex width d ⟨piece.val + 1, by have := piece.isLt; omega⟩)

/-- The genuine leftward spine dart at an original native foot having a predecessor. -/
@[expose] def spineLeftDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex) :
    Graph.Dart (augmentedGraph width hd) :=
  (Piece.spine ⟨vertexRank width d vertex - 1, by have := vertexRank_lt width d vertex.isLt; omega⟩).dart width hd true

/-- The genuine rightward spine dart at an original native foot having a successor. -/
@[expose] def spineRightDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length)
    (hright : vertexRank width d vertex + 1 < d.1.length) : Graph.Dart (augmentedGraph width hd) :=
  (Piece.spine ⟨vertexRank width d vertex, by omega⟩).dart width hd false

/-- The actual leftward spine dart occupies exactly its original numbered native foot. -/
theorem spineLeftDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex) :
    (spineLeftDart width hd vertex hleft).vertex = stationNumber width d (.foot vertex) := by
  rw [spineLeftDart, Piece.dart_vertex]
  change stationNumber width d (.foot (spineVertex width d ⟨vertexRank width d vertex - 1 + 1, _⟩)) = _
  have hi : (⟨vertexRank width d vertex - 1 + 1, by have := vertexRank_lt width d vertex.isLt; omega⟩ : Fin d.1.length) =
      spineRank width d vertex := Fin.ext (by change vertexRank width d vertex - 1 + 1 = vertexRank width d vertex; omega)
  rw [hi, spineVertex_spineRank]

/-- The actual rightward spine dart occupies exactly its original numbered native foot. -/
theorem spineRightDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (vertex : Fin d.1.length)
    (hright : vertexRank width d vertex + 1 < d.1.length) :
    (spineRightDart width hd vertex hright).vertex = stationNumber width d (.foot vertex) := by
  rw [spineRightDart, Piece.dart_vertex]
  change stationNumber width d (.foot (spineVertex width d (spineRank width d vertex))) = _
  rw [spineVertex_spineRank]

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The genuine predecessor spine dart has exactly its actual leftward direction. -/
theorem spineLeftDart_direction (vertex : Fin d.1.length) (hleft : 0 < vertexRank width d vertex) :
    (augmentedDrawing width height hd hfit hhead).direction (spineLeftDart width hd vertex hleft) = octantAngle 4 := by
  rw [spineLeftDart, Piece.dart_direction]
  exact spinePiece_direction width height hd hfit _ true

/-- The genuine successor spine dart has exactly its actual rightward direction. -/
theorem spineRightDart_direction (vertex : Fin d.1.length) (hright : vertexRank width d vertex + 1 < d.1.length) :
    (augmentedDrawing width height hd hfit hhead).direction (spineRightDart width hd vertex hright) = octantAngle 0 := by
  rw [spineRightDart, Piece.dart_direction]
  exact spinePiece_direction width height hd hfit _ false

end Geometry
end PushPuzzle.PushS.Comb

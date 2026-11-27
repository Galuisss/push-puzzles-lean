/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombContraction
public import PushS.CombSourceDarts
import all PushS.CombPieces

/-! The actual source-prefix cutoff reverses precisely the original comb-tree darts. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- A genuine source-fragment piece lies in exactly the retained original edge prefix. -/
theorem Piece.source_number_lt (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (piece : Fin ((edgeCrossings width d edge).length + 1)) :
    (Piece.source edge piece : Piece width G d).number < (sourceBase width hd).edges.length := by
  have hm : Piece.source edge piece ∈ (List.finRange G.edges.length).flatMap
      (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge)) :=
    List.mem_flatMap.mpr ⟨edge, List.mem_finRange _, List.mem_ofFn.mpr ⟨piece, rfl⟩⟩
  simpa only [Piece.number, pieces, List.append_assoc, List.idxOf_append_of_mem hm, sourceBase, List.length_map] using
    List.idxOf_lt_length_of_mem hm

/-- Every actual auxiliary piece lies after the retained source prefix. -/
theorem Piece.tree_number_le (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (htree : piece.treeFlip = true) :
    (sourceBase width hd).edges.length ≤ piece.number := by
  have hnot : piece ∉ (List.finRange G.edges.length).flatMap
      (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge)) := by
    intro hm
    obtain ⟨edge, _, hm⟩ := List.mem_flatMap.mp hm
    obtain ⟨index, rfl⟩ := List.mem_ofFn.mp hm
    cases htree
  simp only [Piece.number, pieces, List.append_assoc, List.idxOf_append_of_notMem hnot, sourceBase, List.length_map]
  omega

/-- Reversing the literal auxiliary suffix flips exactly the actual tree-piece end tags. -/
theorem Piece.suffixReversal_dart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    Graph.Dart.suffixReversal (augmentedGraph width hd) (sourceBase width hd).edges.length (piece.dart width hd side) =
      piece.dart width hd (side ^^ piece.treeFlip) := by
  cases piece with
  | source edge piece =>
    rw [Graph.Dart.suffixReversal_source _ _ _ (Piece.source_number_lt width hd edge piece)]
    simp only [Piece.treeFlip, Bool.xor_false]
  | spine piece =>
    rw [Graph.Dart.suffixReversal_tree _ _ _ (Piece.tree_number_le width hd (.spine piece) rfl)]
    cases side <;> rfl
  | tooth vertex piece =>
    rw [Graph.Dart.suffixReversal_tree _ _ _ (Piece.tree_number_le width hd (.tooth vertex piece) rfl)]
    cases side <;> rfl

/-- The genuine tree tour turns at the exact opposite tree end and at the same original source end. -/
theorem Piece.treeTour_dart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (rotation : Graph.RotationSystem (augmentedGraph width hd))
    (piece : Piece width G d) (side : Bool) :
    (PushPuzzle.Graph.RotationSystem.treeTour rotation) (sourceBase width hd).edges.length (piece.dart width hd side) =
      rotation.rotate (piece.dart width hd (side ^^ piece.treeFlip)) := by
  rw [Graph.RotationSystem.treeTour, Equiv.Perm.mul_apply, Piece.suffixReversal_dart]

/-- Every original token-bearing dart belongs to the exact retained source prefix. -/
theorem dartToken_number_lt_source (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (augmentedGraph width hd)) (token : Token)
    (ht : dartToken width hd dart = some token) : dart.1.val < (sourceBase width hd).edges.length := by
  have htoken : (augmentedPiece width hd dart.1).token dart.2 = some token := ht
  generalize hp : augmentedPiece width hd dart.1 = piece at htoken
  have he : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
  rw [← he]
  cases piece with
  | source edge piece => exact Piece.source_number_lt width hd edge piece
  | spine piece => cases htoken
  | tooth vertex piece => cases htoken

/-- The actual tree tour turns immediately at each original source-fragment dart. -/
theorem treeTour_source_dart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (rotation : Graph.RotationSystem (augmentedGraph width hd))
    (dart : Graph.Dart (augmentedGraph width hd)) (token : Token) (ht : dartToken width hd dart = some token) :
    (PushPuzzle.Graph.RotationSystem.treeTour rotation) (sourceBase width hd).edges.length dart = rotation.rotate dart := by
  rw [Graph.RotationSystem.treeTour, Equiv.Perm.mul_apply,
    Graph.Dart.suffixReversal_source _ _ _ (dartToken_number_lt_source width hd dart token ht)]

end PushPuzzle.PushS.Comb

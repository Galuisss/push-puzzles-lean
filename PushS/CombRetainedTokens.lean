/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRootedTour
public import PushS.CombTourReadout
import all PushS.CombDarts
import all PushS.CombRootedOrientation
import all PushS.CombSourceDarts

/-! The contracted original source prefix retains exactly its actual fragment tokens and original end tags. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The actual source prefix occupies at most the complete original augmented piece array. -/
theorem sourceBase_edgeCount_le (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : (sourceBase width hd).edges.length ≤ (augmentedGraph width hd).edges.length := by
  simp only [sourceBase, augmentedGraph, List.length_map, pieces, List.length_append]
  omega

/-- Every genuine dart in the retained actual source prefix carries one original token. -/
theorem dartToken_some_of_number_lt (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (augmentedGraph width hd))
    (hsource : dart.1.val < (sourceBase width hd).edges.length) : ∃ token, dartToken width hd dart = some token := by
  generalize hp : augmentedPiece width hd dart.1 = piece
  have he : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
  rw [← he] at hsource ⊢
  cases piece with
  | source edge piece => exact ⟨fragmentToken width d edge piece dart.2, Piece.dart_token width hd _ _⟩
  | spine piece => exact False.elim (Nat.not_lt_of_ge (Piece.tree_number_le width hd (.spine piece) rfl) hsource)
  | tooth vertex piece => exact False.elim (Nat.not_lt_of_ge (Piece.tree_number_le width hd (.tooth vertex piece) rfl) hsource)

/-- Read precisely original source coordinates, erasing the original tree suffix. -/
@[expose] def sourceCoordinateToken (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (coordinate : ℕ × Bool) : Option Token :=
  if h : coordinate.1 < (sourceBase width hd).edges.length then
    dartToken width hd (⟨⟨coordinate.1, h.trans_le (sourceBase_edgeCount_le width hd)⟩, coordinate.2⟩)
  else none

/-- The exact original rooted source-coordinate readout agrees with the actual geometric dart's token. -/
theorem sourceCoordinateToken_rootDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    sourceCoordinateToken width hd (Graph.Dart.edgeCoordinates (piece.rootDart width hd side)) =
      dartToken width hd (rootedDartEquiv width hd (piece.rootDart width hd side)) := by
  rw [Piece.rootedDartEquiv_rootDart]
  change (if h : piece.number < (sourceBase width hd).edges.length then
    dartToken width hd (piece.dart width hd side) else none) = _
  cases piece with
  | source edge piece =>
    rw [dite_eq_left (Piece.source_number_lt width hd edge piece)]
    simp only [Piece.treeFlip, Bool.xor_false]
  | spine piece =>
    rw [dite_eq_right (Nat.not_lt_of_ge (Piece.tree_number_le width hd (.spine piece) rfl)), Piece.dart_token]
    rfl
  | tooth vertex piece =>
    rw [dite_eq_right (Nat.not_lt_of_ge (Piece.tree_number_le width hd (.tooth vertex piece) rfl)), Piece.dart_token]
    rfl

/-- Each actual rooted indexed dart retains the exact same original source-coordinate readout. -/
theorem sourceCoordinateToken_rooted (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (rootedGraph width hd)) :
    sourceCoordinateToken width hd (Graph.Dart.edgeCoordinates dart) = dartToken width hd (rootedDartEquiv width hd dart) := by
  have he : (rootedPiece width hd dart.1).rootDart width hd dart.2 = dart := by
    apply Prod.ext
    · apply Fin.ext
      exact (pieces_nodup width G d).idxOf_getElem dart.1.val (by simpa only [rootedGraph, List.length_map] using dart.1.isLt)
    · rfl
  rw [← he]
  exact sourceCoordinateToken_rootDart width hd _ _

/-- Explicitly filtering the tree suffix changes none of the original source-coordinate readout. -/
theorem sourceCoordinateToken_filter (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (coordinates : List (ℕ × Bool)) :
    (coordinates.filter (fun c => decide (c.1 < (sourceBase width hd).edges.length))).filterMap (sourceCoordinateToken width hd) =
      coordinates.filterMap (sourceCoordinateToken width hd) := by
  induction coordinates with
  | nil => rfl
  | cons coordinate tail ih =>
    by_cases h : coordinate.1 < (sourceBase width hd).edges.length
    · simp only [List.filter_cons, h, decide_true, ite_true, List.filterMap_cons, ih]
    · have hnone : sourceCoordinateToken width hd coordinate = none := by rw [sourceCoordinateToken, dite_eq_right h]
      simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, ite_false, List.filterMap_cons, hnone, ih]

/-- Reinsert an actual retained source dart at its unchanged original augmented edge index and end tag. -/
@[expose] def retainedSourceDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (dart : Graph.Dart (contractedGraph width hd hv)) :
    Graph.Dart (augmentedGraph width hd) :=
  (⟨dart.1.val, by
    apply Nat.lt_of_lt_of_le _ (sourceBase_edgeCount_le width hd)
    rw [← contractedGraph_edgeCount width hd hv]
    exact dart.1.isLt⟩, dart.2)

/-- The actual contracted source dart's unchanged coordinates read its same original geometric token. -/
theorem sourceCoordinateToken_retained (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (dart : Graph.Dart (contractedGraph width hd hv)) :
    sourceCoordinateToken width hd (Graph.Dart.edgeCoordinates dart) = dartToken width hd (retainedSourceDart width hd hv dart) := by
  unfold sourceCoordinateToken
  rw [dite_eq_left (by rw [← contractedGraph_edgeCount width hd hv]; exact dart.1.isLt)]
  rfl

/-- The literal original source token of an actual retained indexed dart. -/
@[expose] def retainedToken (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (dart : Graph.Dart (contractedGraph width hd hv)) : Token :=
  (dartToken width hd (retainedSourceDart width hd hv dart)).getD (.tip 0 false)

/-- Every actual retained source dart keeps one and exactly one original token. -/
theorem retainedToken_some (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (dart : Graph.Dart (contractedGraph width hd hv)) :
    dartToken width hd (retainedSourceDart width hd hv dart) = some (retainedToken width hd hv dart) := by
  obtain ⟨token, ht⟩ := dartToken_some_of_number_lt width hd (retainedSourceDart width hd hv dart)
    (by change dart.1.val < _; rw [← contractedGraph_edgeCount width hd hv]; exact dart.1.isLt)
  simp only [retainedToken, ht, Option.getD_some]

/-- Distinct actual retained indexed ends retain distinct original source tokens. -/
theorem retainedToken_injective (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) : Function.Injective (retainedToken width hd hv) := by
  intro left right he
  have hleft := retainedToken_some width hd hv left
  have hright := retainedToken_some width hd hv right
  rw [← he] at hright
  have hdarts := dartToken_some_injective width hd _ _ _ hleft hright
  apply Prod.ext
  · exact Fin.ext (congrArg (fun dart => dart.1.val) hdarts)
  · have hside : left.2 = right.2 := congrArg (fun dart : Graph.Dart (augmentedGraph width hd) => dart.2) hdarts
    exact hside

/-- The unchanged actual retained edge index of one original source fragment. -/
@[expose] def retainedFragmentIndex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (edge : Fin G.edges.length)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) : Fin (contractedGraph width hd hv).edges.length :=
  ⟨(Piece.source edge piece : Piece width G d).number, by
    rw [contractedGraph_edgeCount]
    exact Piece.source_number_lt width hd edge piece⟩

/-- Every retained source-fragment end reads exactly its own original even/odd visit token. -/
theorem retainedToken_fragment (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (edge : Fin G.edges.length)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    retainedToken width hd hv (retainedFragmentIndex width hd hv edge piece, side) = fragmentToken width d edge piece side := by
  apply Option.some.inj
  rw [← retainedToken_some]
  have he : retainedSourceDart width hd hv (retainedFragmentIndex width hd hv edge piece, side) =
      (Piece.source edge piece).dart width hd side := rfl
  rw [he, Piece.dart_token]
  rfl

/-- Every literal original source pair consists of precisely the two ends of one actual native source fragment. -/
theorem sourcePairs_fragment (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (g : NCL.AndOrGraph) {pair : Token × Token}
    (hp : pair ∈ sourcePairs width ⟨g, d⟩) : ∃ (edge : Fin G.edges.length) (piece : Fin ((edgeCrossings width d edge).length + 1)),
      pair = (fragmentToken width d edge piece false, fragmentToken width d edge piece true) := by
  obtain ⟨route, hr, hp⟩ := List.mem_flatMap.mp hp
  have hedge : route.2 < G.edges.length := by rw [← hd.edgeCount]; exact List.snd_lt_of_mem_zipIdx hr
  let edge : Fin G.edges.length := ⟨route.2, hedge⟩
  obtain ⟨index, he⟩ := List.mem_iff_get.mp hp
  let piece : Fin ((edgeCrossings width d edge).length + 1) :=
    ⟨index.val, by rw [← edgeVisits_pairOff_length width d edge]; exact index.isLt⟩
  have hget : (pairOff (edgeVisits width d edge)).getD piece (.tip 0 false, .tip 0 false) = pair := by
    rw [List.getD_eq_getElem _ _ index.isLt]
    exact he
  exact ⟨edge, piece, hget.symm.trans (fragmentToken_pairOff width d edge piece)⟩

/-- Reading any retained source word maps every actual end to its one original token. -/
theorem retainedToken_word (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length) (word : List (Graph.Dart (contractedGraph width hd hv))) :
    (word.map Graph.Dart.edgeCoordinates).filterMap (sourceCoordinateToken width hd) = word.map (retainedToken width hd hv) := by
  induction word with
  | nil => rfl
  | cons dart tail ih => simp only [List.map_cons, List.filterMap_cons, sourceCoordinateToken_retained, retainedToken_some, ih]

/-- Reading the word through the actual inverse tree-end flip preserves precisely the original source tokens. -/
theorem rootedToken_word (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (word : List (Graph.Dart (augmentedGraph width hd))) :
    ((word.map (rootedDartEquiv width hd).symm).map Graph.Dart.edgeCoordinates).filterMap (sourceCoordinateToken width hd) =
      word.filterMap (dartToken width hd) := by
  induction word with
  | nil => rfl
  | cons dart tail ih =>
    have ht := sourceCoordinateToken_rooted width hd ((rootedDartEquiv width hd).symm dart)
    rw [Equiv.apply_symm_apply] at ht
    simp only [List.map_cons, List.filterMap_cons, ht, ih]

end PushPuzzle.PushS.Comb

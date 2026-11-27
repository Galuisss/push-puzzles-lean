/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRootedOrientation
public import PushS.CombFragmentTokens

/-! Exact named piece darts in the actual native augmented graph and their literal source tokens. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The literal original position of an actual piece in the complete emitted augmented edge array. -/
@[expose] def Piece.number {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} (piece : Piece width G d) : ℕ :=
  (pieces width G d).idxOf piece

/-- Every actual named piece has an in-bounds original edge-array position. -/
theorem Piece.number_lt {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} (piece : Piece width G d) :
    piece.number < (pieces width G d).length := List.idxOf_lt_length_of_mem (pieces_complete width G d piece)

/-- Original indexed piece numbers retain every actual source and comb-tree identity. -/
theorem Piece.number_injective {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} :
    Function.Injective (Piece.number (width := width) (G := G) (d := d)) := by
  intro a b he
  exact (List.idxOf_inj (pieces_complete width G d a)).mp he

/-- The literal original indexed dart at one actual geometric piece end. -/
@[expose] def Piece.dart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) : Graph.Dart (augmentedGraph width hd) :=
  (⟨piece.number, by simpa only [augmentedGraph, List.length_map] using piece.number_lt⟩, side)

/-- The same original indexed piece dart in the explicitly leaf-to-root oriented graph. -/
@[expose] def Piece.rootDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) : Graph.Dart (rootedGraph width hd) :=
  (⟨piece.number, by simpa only [rootedGraph, List.length_map] using piece.number_lt⟩, side)

/-- Reading the actual edge-array position of a named geometric dart returns that same original piece. -/
theorem Piece.augmentedPiece_dart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    augmentedPiece width hd (piece.dart width hd side).1 = piece := by
  simp only [augmentedPiece, Piece.dart, Piece.number, List.get_eq_getElem, List.getElem_idxOf]

/-- Reading the rooted position retains the exact same original source or tree piece. -/
theorem Piece.rootedPiece_rootDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    rootedPiece width hd (piece.rootDart width hd side).1 = piece := by
  simp only [rootedPiece, Piece.rootDart, Piece.number, List.get_eq_getElem, List.getElem_idxOf]

/-- Every actual native augmented dart is exactly its genuine stored piece and Boolean end. -/
theorem Piece.dart_augmentedPiece (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (augmentedGraph width hd)) :
    (augmentedPiece width hd dart.1).dart width hd dart.2 = dart := by
  apply Prod.ext
  · apply Fin.ext
    exact (pieces_nodup width G d).idxOf_getElem dart.1.val (by
      simpa only [augmentedGraph, List.length_map] using dart.1.isLt)
  · rfl

/-- Genuine named piece darts have exactly their actual stored station-number endpoints. -/
theorem Piece.dart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    (piece.dart width hd side).vertex = stationNumber width d (piece.station width hd side) := by
  rw [augmented_dart_vertex, Piece.augmentedPiece_dart]
  rfl

/-- Rooted named piece darts retain their exact leaf-to-root station-number endpoints. -/
theorem Piece.rootDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    (piece.rootDart width hd side).vertex = stationNumber width d (piece.rootStation width hd side) := by
  rw [rooted_dart_vertex, Piece.rootedPiece_rootDart]
  rfl

/-- The explicit auxiliary edge-end flip acts at the same genuine named piece position. -/
theorem Piece.rootedDartEquiv_rootDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    rootedDartEquiv width hd (piece.rootDart width hd side) = piece.dart width hd (side ^^ piece.treeFlip) := by
  apply Prod.ext
  · rfl
  · change (side ^^ (rootedPiece width hd (piece.rootDart width hd side).1).treeFlip) = (side ^^ piece.treeFlip)
    rw [Piece.rootedPiece_rootDart]

/-- Named indexed darts identify precisely their original piece and Boolean end tag. -/
theorem Piece.dart_inj (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (left right : Piece width G d) (a b : Bool) :
    left.dart width hd a = right.dart width hd b ↔ left = right ∧ a = b := by
  constructor
  · intro he
    have hp := congrArg (fun dart : Graph.Dart (augmentedGraph width hd) => augmentedPiece width hd dart.1) he
    rw [Piece.augmentedPiece_dart, Piece.augmentedPiece_dart] at hp
    exact ⟨hp, congrArg Prod.snd he⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- Each actual source-fragment end keeps its original visit token; auxiliary tree darts contribute no token. -/
@[expose] def Piece.token {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} : Piece width G d → Bool → Option Token
  | .source edge piece, side => some (fragmentToken width d edge piece side)
  | .spine _, _ => none
  | .tooth _ _, _ => none

/-- Exactly the genuine auxiliary tree pieces have no source-contour token. -/
theorem Piece.token_none {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing} (piece : Piece width G d) (side : Bool) :
    piece.token side = none ↔ piece.treeFlip = true := by
  cases piece <;> simp [Piece.token, Piece.treeFlip]

/-- A literal retained source token identifies the exact actual named piece dart. -/
theorem Piece.token_some_injective {width : ℕ} {G : Graph} {d : Graph.OrthogonalDrawing}
    (left right : Piece width G d) (a b : Bool) (token : Token)
    (hl : left.token a = some token) (hr : right.token b = some token) : left = right ∧ a = b := by
  cases left with
  | source e p =>
    cases right with
    | source f q =>
      have heq : fragmentToken width d e p a = fragmentToken width d f q b := Option.some.inj (hl.trans hr.symm)
      have hedge : e = f := Fin.ext (fragmentToken_same_edge width d e f p q a b heq)
      subst f
      obtain ⟨rfl, rfl⟩ := fragmentToken_same_end width d e p q a b heq
      exact ⟨rfl, rfl⟩
    | spine _ => simp [Piece.token] at hr
    | tooth _ _ => simp [Piece.token] at hr
  | spine _ => simp [Piece.token] at hl
  | tooth _ _ => simp [Piece.token] at hl

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- Reading an actual named dart in the geometric drawing retains its exact genuine outgoing piece ray. -/
theorem Piece.dart_germ (piece : Piece width G d) (side : Bool) :
    (augmentedDrawing width height hd hfit hhead).germ (piece.dart width hd side) =
      (piece.route width height hd hfit hhead).germ side := by
  change ((augmentedPiece width hd (piece.dart width hd side).1).route width height hd hfit hhead).germ side = _
  rw [Piece.augmentedPiece_dart]

/-- The actual named indexed dart has precisely the genuine route's angular direction. -/
theorem Piece.dart_direction (piece : Piece width G d) (side : Bool) :
    (augmentedDrawing width height hd hfit hhead).direction (piece.dart width hd side) =
      ((piece.route width height hd hfit hhead).germ side).arg := by
  change (((augmentedDrawing width height hd hfit hhead).germ (piece.dart width hd side)).arg : Real.Angle) = _
  rw [Piece.dart_germ]

end Geometry
end PushPuzzle.PushS.Comb

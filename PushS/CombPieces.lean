/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSpineContacts

/-! The finite indexed edge family of the actual source-fragment and comb-tree embedding. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- One genuine source fragment, lower spine piece, or tooth piece of the actual augmented graph. -/
inductive Piece (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) where
  | source (edge : Fin G.edges.length) (piece : Fin ((edgeCrossings width d edge).length + 1))
  | spine (piece : Fin (d.1.length - 1))
  | tooth (vertex : Fin d.1.length) (piece : Fin ((toothCrossings width d vertex).length + 1))
  deriving DecidableEq

/-- Actual source fragments precede the bottom spine and bottom-to-top native tooth pieces. -/
@[expose] def pieces (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) : List (Piece width G d) :=
  (List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source edge)) ++
    List.ofFn Piece.spine ++
    (List.finRange d.1.length).flatMap (fun vertex => List.ofFn (Piece.tooth vertex))

/-- The actual augmented edge array retains every genuine source and comb-tree piece. -/
theorem pieces_complete (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) (piece : Piece width G d) :
    piece ∈ pieces width G d := by
  simp only [pieces, List.mem_append]
  cases piece with
  | source edge piece =>
    exact Or.inl (Or.inl (List.mem_flatMap.mpr ⟨edge, List.mem_finRange _, List.mem_ofFn.mpr ⟨piece, rfl⟩⟩))
  | spine piece => exact Or.inl (Or.inr (List.mem_ofFn.mpr ⟨piece, rfl⟩))
  | tooth vertex piece =>
    exact Or.inr (List.mem_flatMap.mpr ⟨vertex, List.mem_finRange _, List.mem_ofFn.mpr ⟨piece, rfl⟩⟩)

private theorem source_pieces_nodup (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) :
    ((List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge))).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro edge _
    exact List.nodup_ofFn.mpr (fun _ _ h => by cases h; rfl)
  · apply List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_finRange _)
    apply List.disjoint_left.mpr
    intro piece hp hq
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨q, hq⟩ := List.mem_ofFn.mp hq
    cases hq
    exact hab rfl

private theorem tooth_pieces_nodup (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) :
    ((List.finRange d.1.length).flatMap (fun vertex => List.ofFn (Piece.tooth (width := width) (G := G) vertex))).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro vertex _
    exact List.nodup_ofFn.mpr (fun _ _ h => by cases h; rfl)
  · apply List.Pairwise.imp (fun {a b} hab => ?_) (List.nodup_finRange _)
    apply List.disjoint_left.mpr
    intro piece hp hq
    obtain ⟨p, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨q, hq⟩ := List.mem_ofFn.mp hq
    cases hq
    exact hab rfl

/-- Distinct actual edge-array positions retain distinct genuine piece identities. -/
theorem pieces_nodup (width : ℕ) (G : Graph) (d : Graph.OrthogonalDrawing) : (pieces width G d).Nodup := by
  have hs := source_pieces_nodup width G d
  have ht := tooth_pieces_nodup width G d
  have hb : (List.ofFn (Piece.spine (width := width) (G := G) (d := d))).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => Piece.spine.inj h)
  have hsb : List.Disjoint
      ((List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge)))
      (List.ofFn Piece.spine) := by
    apply List.disjoint_left.mpr
    intro piece
    cases piece <;> simp
  have hst : List.Disjoint
      ((List.finRange G.edges.length).flatMap (fun edge => List.ofFn (Piece.source (width := width) (d := d) edge)))
      ((List.finRange d.1.length).flatMap (fun vertex => List.ofFn (Piece.tooth vertex))) := by
    apply List.disjoint_left.mpr
    intro piece
    cases piece <;> simp
  have hbt : List.Disjoint (List.ofFn (Piece.spine (width := width) (G := G) (d := d)))
      ((List.finRange d.1.length).flatMap (fun vertex => List.ofFn (Piece.tooth vertex))) := by
    apply List.disjoint_left.mpr
    intro piece
    cases piece <;> simp
  exact (hs.append hb hsb).append ht (List.disjoint_append_left.mpr ⟨hst, hbt⟩)

/-- The exact named station at one Boolean end of an actual augmented edge piece. -/
@[expose] def Piece.station (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) : Piece width G d → Bool → Station width d
  | .source edge piece, side => edgeStation width hd edge (if side then piece.succ else piece.castSucc)
  | .spine piece, side => .foot (if side then spineRight width d piece else spineLeft width d piece)
  | .tooth vertex piece, side => toothStation width d vertex (if side then piece.succ else piece.castSucc)

/-- The genuine polygonal route belonging to one actual augmented indexed edge. -/
@[expose] noncomputable def Piece.route (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (hhead : ∀ edge : Fin G.edges.length,
      (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) : Piece width G d → Cslib.Polygonal.Route
  | .source edge piece => edgeFragment width height hd hfit edge (hhead edge) piece
  | .spine piece => spinePiece width d piece
  | .tooth vertex piece => toothPiece width d vertex piece

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- Every actual piece has precisely its native named station endpoints. -/
theorem Piece.route_endpoint (piece : Piece width G d) (side : Bool) :
    (piece.route width height hd hfit hhead).endpoint side =
      complexPoint (stationPoint width d (piece.station width hd side)) := by
  cases piece with
  | source edge piece => exact edgeFragment_station_endpoint width height hd hfit edge (hhead edge) piece side
  | spine piece => exact spinePiece_endpoint width d piece side
  | tooth vertex piece => exact toothPiece_endpoint width d vertex piece side

/-- Every route in the actual indexed augmented family is a simple polygonal route. -/
theorem Piece.simple (piece : Piece width G d) : (piece.route width height hd hfit hhead).IsSimple := by
  cases piece with
  | source edge piece => exact edgeFragment_simple width height hd hfit edge (hhead edge) piece
  | spine piece => exact spinePiece_simple width height hd hfit piece
  | tooth vertex piece => exact toothPiece_simple width height hd hfit vertex piece

/-- Each named station on any actual augmented edge is one of that edge's exact named ends. -/
theorem Piece.station_contact (piece : Piece width G d) (i : Fin (piece.route width height hd hfit hhead).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (station : Station width d)
    (he : (piece.route width height hd hfit hhead).eval i t = complexPoint (stationPoint width d station)) :
    ∃ side, (piece.route width height hd hfit hhead).AtEnd i t side ∧ piece.station width hd side = station := by
  cases piece with
  | source edge piece => exact edgeFragment_station_contact width height hd hfit edge (hhead edge) piece i ht station he
  | spine piece => exact spinePiece_station_contact width height hd hfit piece i ht station he
  | tooth vertex piece => exact toothPiece_station_contact width height hd hfit vertex piece i ht station he

end Geometry
end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombDarts
public import PushS.CombCrossingDirections
import all PushS.CombDarts

/-! Canonical actual source darts at native tips and genuine crossing-side occurrences. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- Read the original source token of an actual indexed augmented dart. -/
@[expose] def dartToken (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (dart : Graph.Dart (augmentedGraph width hd)) : Option Token :=
  (augmentedPiece width hd dart.1).token dart.2

/-- Actual named piece darts read precisely their own original source token. -/
theorem Piece.dart_token (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (piece : Piece width G d) (side : Bool) :
    dartToken width hd (piece.dart width hd side) = piece.token side := by
  rw [dartToken, Piece.augmentedPiece_dart]
  rfl

/-- The literal source token identifies its unique actual indexed augmented dart. -/
theorem dartToken_some_injective (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (left right : Graph.Dart (augmentedGraph width hd)) (token : Token)
    (hl : dartToken width hd left = some token) (hr : dartToken width hd right = some token) : left = right := by
  have h := Piece.token_some_injective (augmentedPiece width hd left.1) (augmentedPiece width hd right.1) left.2 right.2 token hl hr
  rw [← Piece.dart_augmentedPiece width hd left, ← Piece.dart_augmentedPiece width hd right]
  exact (Piece.dart_inj width hd _ _ _ _).mpr h

/-- The original false native endpoint is the first literal source station. -/
theorem edgeStation_zero (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    edgeStation width hd edge 0 = edgeTipStation width hd edge false := by
  simp only [edgeStation, edgeStations, List.get_eq_getElem, Fin.val_zero, List.cons_append, List.getElem_cons_zero]

/-- The original true native endpoint is the last literal source station. -/
theorem edgeStation_last (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    edgeStation width hd edge (Fin.last ((edgeCrossings width d edge).length + 1)) = edgeTipStation width hd edge true := by
  let index := (edgeCrossings width d edge).length + 1
  have hi : index < (edgeStations width hd edge).length := by rw [edgeStations_length]; omega
  have hget : edgeStation width hd edge (Fin.last ((edgeCrossings width d edge).length + 1)) =
      (edgeStations width hd edge).getD index (edgeTipStation width hd edge true) := by
    rw [List.getD_eq_getElem _ _ hi]
    rfl
  rw [hget]
  unfold edgeStations
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_map, List.length_attach]; exact le_rfl)]
  simp only [List.length_cons, List.length_map, List.length_attach, index, Nat.sub_self, List.getD_cons_zero]

/-- The genuine retained source-fragment dart at its original native false or true endpoint. -/
@[expose] def sourceTipDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) : Graph.Dart (augmentedGraph width hd) :=
  (Piece.source edge (if side then Fin.last (edgeCrossings width d edge).length else 0)).dart width hd side

/-- The actual native source-tip dart retains exactly its original edge and end token. -/
theorem sourceTipDart_token (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) :
    dartToken width hd (sourceTipDart width hd edge side) = some (.tip edge.val side) := by
  cases side <;> simp [sourceTipDart, Piece.dart_token, Piece.token, fragmentToken_first, fragmentToken_last]

/-- The genuine native source-tip dart occupies precisely its original named source station. -/
theorem sourceTipDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool) :
    (sourceTipDart width hd edge side).vertex = stationNumber width d (edgeTipStation width hd edge side) := by
  rw [sourceTipDart, Piece.dart_vertex]
  cases side <;> simp only [Piece.station, Bool.false_eq_true, ite_false, ite_true, Fin.castSucc_zero, Fin.succ_last,
    edgeStation_zero, edgeStation_last]

/-- Actual native source-tip darts retain their original edge identity and Boolean endpoint. -/
theorem sourceTipDart_inj (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (left right : Fin G.edges.length) (a b : Bool) :
    sourceTipDart width hd left a = sourceTipDart width hd right b ↔ left = right ∧ a = b := by
  constructor
  · intro he
    have h := congrArg (dartToken width hd) he
    rw [sourceTipDart_token, sourceTipDart_token] at h
    have hp := Token.tip.inj (Option.some.inj h)
    exact ⟨Fin.ext hp.1, hp.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- The actual source dart for one original crossing occurrence and one literal contour side. -/
@[expose] def edgeCrossingDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : Fin (edgeCrossings width d edge).length) (returnSide : Bool) : Graph.Dart (augmentedGraph width hd) :=
  let side := returnSide ^^ (edgeCrossingHit width d edge hit).val.forward
  (Piece.source edge (if side then hit.castSucc else hit.succ)).dart width hd side

/-- Each canonical crossing dart carries exactly the original ascending or returning contour token. -/
theorem edgeCrossingDart_token (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : Fin (edgeCrossings width d edge).length) (returnSide : Bool) :
    dartToken width hd (edgeCrossingDart width hd edge hit returnSide) =
      some ((edgeCrossingHit width d edge hit).val.token returnSide) := by
  cases hforward : (edgeCrossingHit width d edge hit).val.forward <;> cases returnSide <;>
    simp only [edgeCrossingDart, Piece.dart_token, Piece.token, hforward, Bool.xor_false, Bool.xor_true,
      Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
  · rw [fragmentToken_crossing_after]
    change some (((edgeCrossingHit width d edge hit).val).token (edgeCrossingHit width d edge hit).val.forward) = _
    rw [hforward]
  · rw [fragmentToken_crossing_before]
    change some (((edgeCrossingHit width d edge hit).val).token (!(edgeCrossingHit width d edge hit).val.forward)) = _
    rw [hforward]
    rfl
  · rw [fragmentToken_crossing_before]
    change some (((edgeCrossingHit width d edge hit).val).token (!(edgeCrossingHit width d edge hit).val.forward)) = _
    rw [hforward]
    rfl
  · rw [fragmentToken_crossing_after]
    change some (((edgeCrossingHit width d edge hit).val).token (edgeCrossingHit width d edge hit).val.forward) = _
    rw [hforward]

/-- Both canonical crossing-side darts occupy exactly the same original numbered crossing station. -/
theorem edgeCrossingDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hit : Fin (edgeCrossings width d edge).length) (returnSide : Bool) :
    (edgeCrossingDart width hd edge hit returnSide).vertex =
      stationNumber width d (.crossing (edgeCrossingHit width d edge hit)) := by
  unfold edgeCrossingDart
  rw [Piece.dart_vertex]
  cases (returnSide ^^ (edgeCrossingHit width d edge hit).val.forward) <;>
    simp only [Piece.station, Bool.false_eq_true, ite_false, ite_true, Fin.succ_castSucc, edgeStation_crossing]

/-- The exact original finite source edge of a genuine global crossing occurrence. -/
@[expose] def crossingEdge (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) : Fin G.edges.length :=
  ⟨hit.val.edge, by rw [← hd.edgeCount]; exact crossing_edge_lt width d hit.property⟩

private theorem crossing_mem_source (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) :
    hit.val ∈ edgeCrossings width d (crossingEdge width hd hit) := by
  apply (edgeCrossings_perm width d _).mem_iff.mpr
  exact List.mem_filter.mpr ⟨hit.property, by simp [crossingEdge]⟩

/-- The literal original encounter index of one global crossing on its own source edge. -/
@[expose] def crossingHitIndex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) :
    Fin (edgeCrossings width d (crossingEdge width hd hit)).length :=
  ⟨(edgeCrossings width d (crossingEdge width hd hit)).idxOf hit.val, by
    exact List.idxOf_lt_length_of_mem (crossing_mem_source width hd hit)⟩

/-- Re-reading that canonical original encounter index retains its exact complete global occurrence. -/
theorem edgeCrossingHit_index (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) :
    edgeCrossingHit width d (crossingEdge width hd hit) (crossingHitIndex width hd hit) = hit := by
  apply Subtype.ext
  simp only [edgeCrossingHit, crossingHitIndex, List.get_eq_getElem, List.getElem_idxOf]

/-- The actual indexed source dart of one genuine global crossing and original contour side. -/
@[expose] def crossingDart (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) (returnSide : Bool) :
    Graph.Dart (augmentedGraph width hd) :=
  edgeCrossingDart width hd (crossingEdge width hd hit) (crossingHitIndex width hd hit) returnSide

/-- The named global crossing dart reads exactly its own original marked-side token. -/
theorem crossingDart_token (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) (returnSide : Bool) :
    dartToken width hd (crossingDart width hd hit returnSide) = some (hit.val.token returnSide) := by
  rw [crossingDart, edgeCrossingDart_token, edgeCrossingHit_index]

/-- The named global crossing dart occupies exactly its original physical numbered station. -/
theorem crossingDart_vertex (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hit : {c // c ∈ crossings width d}) (returnSide : Bool) :
    (crossingDart width hd hit returnSide).vertex = stationNumber width d (.crossing hit) := by
  rw [crossingDart, edgeCrossingDart_vertex, edgeCrossingHit_index]

/-- Actual marked source darts retain the complete original crossing occurrence and contour-side tag. -/
theorem crossingDart_inj (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (left right : {c // c ∈ crossings width d}) (a b : Bool) :
    crossingDart width hd left a = crossingDart width hd right b ↔ left = right ∧ a = b := by
  constructor
  · intro he
    have h := congrArg (dartToken width hd) he
    rw [crossingDart_token, crossingDart_token] at h
    have hp := Token.mark.inj (Option.some.inj h)
    have hcross := crossings_key_injective width d left.property right.property hp.1 hp.2.1 hp.2.2.1
    exact ⟨Subtype.ext hcross, hp.2.2.2⟩
  · rintro ⟨rfl, rfl⟩
    rfl

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin G.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- Each actual native source-tip dart has exactly the original compiler tangent's clockwise direction. -/
theorem sourceTipDart_direction (edge : Fin G.edges.length) (side : Bool) :
    (augmentedDrawing width height hd hfit hhead).direction (sourceTipDart width hd edge side) =
      octantAngle (tangentOctant (outgoingVector width d ⟨edge.val, side⟩)) := by
  rw [sourceTipDart, Piece.dart_direction]
  change (((edgeFragment width height hd hfit edge (hhead edge)
    (if side then Fin.last (edgeCrossings width d edge).length else 0)).germ side).arg : Real.Angle) = _
  rw [edgeFragment_native_arg]
  exact tangentKey_direction _ (outgoingVector_shape width hd edge (hhead edge) side)
    (outgoingVector_x_ne_zero width hd edge (hhead edge) side)

/-- Canonical original crossing-side darts retain precisely the actual left or right source-ray octants. -/
theorem edgeCrossingDart_direction (edge : Fin G.edges.length) (hit : Fin (edgeCrossings width d edge).length)
    (returnSide : Bool) :
    if returnSide then
      ((augmentedDrawing width height hd hfit hhead).direction (edgeCrossingDart width hd edge hit returnSide) = octantAngle 0 ∨
        (augmentedDrawing width height hd hfit hhead).direction (edgeCrossingDart width hd edge hit returnSide) = octantAngle 7)
    else
      ((augmentedDrawing width height hd hfit hhead).direction (edgeCrossingDart width hd edge hit returnSide) = octantAngle 3 ∨
        (augmentedDrawing width height hd hfit hhead).direction (edgeCrossingDart width hd edge hit returnSide) = octantAngle 4) := by
  let side := returnSide ^^ (edgeCrossingHit width d edge hit).val.forward
  have hflag : (if side then !(edgeCrossingHit width d edge hit).val.forward else (edgeCrossingHit width d edge hit).val.forward) = returnSide := by
    dsimp only [side]
    exact (show ∀ a b : Bool, (if (a ^^ b) then !b else b) = a from by decide) returnSide _
  have h := edgeFragment_crossing_direction width height hd hfit edge (hhead edge) hit side
  rw [hflag] at h
  have hdir : (augmentedDrawing width height hd hfit hhead).direction (edgeCrossingDart width hd edge hit returnSide) =
      (((edgeFragment width height hd hfit edge (hhead edge) (if side then hit.castSucc else hit.succ)).germ side).arg : Real.Angle) := by
    unfold edgeCrossingDart
    exact Piece.dart_direction width height hd hfit hhead _ _
  rw [← hdir] at h
  exact h

/-- The exact global crossing's ascending and returning source darts retain their genuine clockwise side directions. -/
theorem crossingDart_direction (hit : {c // c ∈ crossings width d}) (returnSide : Bool) :
    if returnSide then
      ((augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit returnSide) = octantAngle 0 ∨
        (augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit returnSide) = octantAngle 7)
    else
      ((augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit returnSide) = octantAngle 3 ∨
        (augmentedDrawing width height hd hfit hhead).direction (crossingDart width hd hit returnSide) = octantAngle 4) :=
  edgeCrossingDart_direction width height hd hfit hhead (crossingEdge width hd hit) (crossingHitIndex width hd hit) returnSide

end Geometry

end PushPuzzle.PushS.Comb

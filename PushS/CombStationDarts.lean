/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSpineDarts
import all PushS.CombDarts

/-! Complete incident-dart fibers at the actual native tips, crossings and comb feet. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- A named source tip is exactly the original listed graph's incident native vertex. -/
theorem edgeTipStation_eq_tip_iff (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) (side : Bool)
    (vertex : Fin d.1.length) :
    edgeTipStation width hd edge side = .tip vertex ↔
      Graph.Dart.vertex (edge, side) = G.vertices[vertex.val]'(by rw [← hd.vertexCount]; exact vertex.isLt) := by
  have hv : vertex.val < G.vertices.length := by rw [← hd.vertexCount]; exact vertex.isLt
  have hm : Graph.Dart.vertex (edge, side) ∈ G.vertices := by
    have h := hd.endpointsDeclared G.edges[edge] (List.getElem_mem edge.isLt)
    rw [Graph.Dart.edge_eq_vertices edge] at h
    cases side
    · exact h.1
    · exact h.2
  simp only [edgeTipStation, Station.tip.injEq, Fin.ext_iff]
  constructor
  · intro he
    have h := List.getElem_idxOf (List.idxOf_lt_length_of_mem hm)
    simpa only [he] using h.symm
  · intro he
    rw [he]
    exact hd.labelsNodup.idxOf_getElem vertex.val hv

private theorem source_dart_cases (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
    (∃ nativeSide, (Piece.source edge piece).dart width hd side = sourceTipDart width hd edge nativeSide) ∨
      ∃ hit returnSide, (Piece.source edge piece).dart width hd side = crossingDart width hd hit returnSide := by
  have ht := fragmentToken_mem width d edge piece side
  have htoken : dartToken width hd ((Piece.source edge piece).dart width hd side) =
      some (fragmentToken width d edge piece side) := by rw [Piece.dart_token]; rfl
  rcases (edgeVisits_mem width d edge _).mp ht with ht | ht | ⟨c, hc, _, ht⟩
  · exact Or.inl ⟨false, dartToken_some_injective width hd _ _ _
      (htoken.trans (congrArg some ht)) (sourceTipDart_token width hd edge false)⟩
  · exact Or.inl ⟨true, dartToken_some_injective width hd _ _ _
      (htoken.trans (congrArg some ht)) (sourceTipDart_token width hd edge true)⟩
  · rcases ht with ht | ht
    · exact Or.inr ⟨⟨c, hc⟩, false, dartToken_some_injective width hd _ _ _
        (htoken.trans (congrArg some ht)) (crossingDart_token width hd ⟨c, hc⟩ false)⟩
    · exact Or.inr ⟨⟨c, hc⟩, true, dartToken_some_injective width hd _ _ _
        (htoken.trans (congrArg some ht)) (crossingDart_token width hd ⟨c, hc⟩ true)⟩

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)

include hd hfit in
private theorem tooth_station_injective (vertex : Fin d.1.length) :
    Function.Injective (toothStation width d vertex) := by
  intro a b he
  exact (toothStation_strictMono width height hd hfit vertex).injective
    (congrArg (fun station => (stationPoint width d station).2) he)

private theorem tooth_owner (vertex : Fin d.1.length)
    (index : Fin ((toothCrossings width d vertex).length + 2)) :
    (toothStation width d vertex index).tooth = vertex :=
  toothStations_owner width d vertex (List.get_mem _ _)

include hfit in
private theorem tooth_dart_tip (vertex target : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool)
    (he : toothStation width d vertex (if side then piece.succ else piece.castSucc) = .tip target) :
    (Piece.tooth vertex piece).dart width hd side = toothTipDart width hd target := by
  have ho := tooth_owner width vertex (if side then piece.succ else piece.castSucc)
  rw [he] at ho
  change target = vertex at ho
  subst vertex
  have hi := tooth_station_injective width height hd hfit target (he.trans (toothStation_last width d target).symm)
  cases side with
  | false =>
    have hp := piece.isLt
    have hval := congrArg Fin.val hi
    simp only [Bool.false_eq_true, ite_false, Fin.val_castSucc, Fin.val_last] at hval
    omega
  | true =>
    have hp : piece = Fin.last (toothCrossings width d target).length := by
      apply Fin.ext
      have hval := congrArg Fin.val hi
      simp only [ite_true, Fin.val_succ, Fin.val_last] at hval
      exact Nat.add_right_cancel hval
    rw [hp]
    rfl

include hfit in
private theorem tooth_dart_foot (vertex target : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool)
    (he : toothStation width d vertex (if side then piece.succ else piece.castSucc) = .foot target) :
    (Piece.tooth vertex piece).dart width hd side = toothFootDart width hd target := by
  have ho := tooth_owner width vertex (if side then piece.succ else piece.castSucc)
  rw [he] at ho
  change target = vertex at ho
  subst vertex
  have hi := tooth_station_injective width height hd hfit target (he.trans (toothStation_first width d target).symm)
  cases side with
  | false =>
    have hp : piece = 0 := by
      apply Fin.ext
      simpa only [Bool.false_eq_true, ite_false, Fin.val_castSucc, Fin.val_zero] using congrArg Fin.val hi
    rw [hp]
    rfl
  | true =>
    have hval := congrArg Fin.val hi
    simp only [ite_true, Fin.val_succ, Fin.val_zero] at hval
    omega

include hfit in
private theorem tooth_dart_crossing (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool)
    (hit : {c // c ∈ crossings width d})
    (he : toothStation width d vertex (if side then piece.succ else piece.castSucc) = .crossing hit) :
    (Piece.tooth vertex piece).dart width hd side = toothCrossingDart width hd hit (!side) := by
  have ho := tooth_owner width vertex (if side then piece.succ else piece.castSucc)
  rw [he] at ho
  subst vertex
  have hi := tooth_station_injective width height hd hfit (.crossing hit : Station width d).tooth
    (he.trans (by rw [toothStation_crossing, toothCrossingHit_index]))
  have hval := congrArg Fin.val hi
  cases side with
  | false =>
    have hp : piece = (toothHitIndex width d hit).succ := by
      apply Fin.ext
      exact hval
    rw [hp]
    rfl
  | true =>
    have hp : piece = (toothHitIndex width d hit).castSucc := by
      apply Fin.ext
      simp only [ite_true, Fin.val_succ, Fin.val_castSucc] at hval
      exact Nat.add_right_cancel hval
    rw [hp]
    rfl

private theorem spine_dart_foot (piece : Fin (d.1.length - 1)) (side : Bool) (target : Fin d.1.length)
    (he : (Piece.spine piece).station width hd side = .foot target) :
    (∃ hleft, (Piece.spine piece).dart width hd side = spineLeftDart width hd target hleft) ∨
      ∃ hright, (Piece.spine piece).dart width hd side = spineRightDart width hd target hright := by
  have hp := piece.isLt
  cases side with
  | false =>
    have hv : spineLeft width d piece = target := Station.foot.inj he
    have hr : vertexRank width d target = piece.val := by rw [← hv, spineLeft_rank]
    have hright : vertexRank width d target + 1 < d.1.length := by omega
    refine Or.inr ⟨hright, ?_⟩
    have hi : piece = ⟨vertexRank width d target, by omega⟩ := Fin.ext hr.symm
    rw [hi]
    rfl
  | true =>
    have hv : spineRight width d piece = target := Station.foot.inj he
    have hr : vertexRank width d target = piece.val + 1 := by rw [← hv, spineRight_rank]
    have hleft : 0 < vertexRank width d target := by omega
    refine Or.inl ⟨hleft, ?_⟩
    have hi : piece = ⟨vertexRank width d target - 1, by omega⟩ := Fin.ext (by dsimp; omega)
    rw [hi]
    rfl

private theorem piece_station_of_vertex (dart : Graph.Dart (augmentedGraph width hd))
    (station : Station width d) (hv : dart.vertex = stationNumber width d station) :
    (augmentedPiece width hd dart.1).station width hd dart.2 = station := by
  apply stationNumber_injective width d
  rw [← Piece.dart_vertex, Piece.dart_augmentedPiece]
  exact hv

include hfit in
/-- A native tip has precisely its original source incidences and the final downward tooth dart. -/
theorem dart_vertex_tip_iff (dart : Graph.Dart (augmentedGraph width hd)) (vertex : Fin d.1.length) :
    dart.vertex = stationNumber width d (.tip vertex) ↔
      (∃ native : Graph.Dart G,
        native.vertex = G.vertices[vertex.val]'(by rw [← hd.vertexCount]; exact vertex.isLt) ∧
          dart = sourceTipDart width hd native.1 native.2) ∨ dart = toothTipDart width hd vertex := by
  constructor
  · intro hv
    have hs := piece_station_of_vertex width hd dart (.tip vertex) hv
    generalize hp : augmentedPiece width hd dart.1 = piece at hs
    have hpiece : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
    cases piece with
    | source edge piece =>
      rcases source_dart_cases width hd edge piece dart.2 with ⟨side, he⟩ | ⟨hit, side, he⟩
      · have ht : edgeTipStation width hd edge side = .tip vertex := by
          apply stationNumber_injective width d
          rw [← sourceTipDart_vertex, ← he, hpiece]
          exact hv
        exact Or.inl ⟨(edge, side), (edgeTipStation_eq_tip_iff width hd edge side vertex).mp ht, hpiece.symm.trans he⟩
      · have ht : Station.crossing hit = .tip vertex := by
          apply stationNumber_injective width d
          rw [← crossingDart_vertex width hd hit side, ← he, hpiece]
          exact hv
        cases ht
    | spine piece => cases hs
    | tooth owner piece =>
      exact Or.inr (hpiece.symm.trans (tooth_dart_tip width height hd hfit owner vertex piece dart.2 hs))
  · rintro (⟨native, hn, rfl⟩ | rfl)
    · rw [sourceTipDart_vertex, (edgeTipStation_eq_tip_iff width hd native.1 native.2 vertex).mpr hn]
    · exact toothTipDart_vertex width hd vertex

include hfit in
/-- A genuine crossing has exactly the two retained source darts and the two adjacent tooth darts. -/
theorem dart_vertex_crossing_iff (dart : Graph.Dart (augmentedGraph width hd)) (hit : {c // c ∈ crossings width d}) :
    dart.vertex = stationNumber width d (.crossing hit) ↔
      dart = crossingDart width hd hit false ∨ dart = crossingDart width hd hit true ∨
        dart = toothCrossingDart width hd hit false ∨ dart = toothCrossingDart width hd hit true := by
  constructor
  · intro hv
    have hs := piece_station_of_vertex width hd dart (.crossing hit) hv
    generalize hp : augmentedPiece width hd dart.1 = piece at hs
    have hpiece : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
    cases piece with
    | source edge piece =>
      rcases source_dart_cases width hd edge piece dart.2 with ⟨side, he⟩ | ⟨other, side, he⟩
      · have ht : edgeTipStation width hd edge side = .crossing hit := by
          apply stationNumber_injective width d
          rw [← sourceTipDart_vertex, ← he, hpiece]
          exact hv
        cases ht
      · have ht : other = hit := Station.crossing.inj (stationNumber_injective width d (by
          rw [← crossingDart_vertex width hd other side, ← he, hpiece]
          exact hv))
        subst other
        cases side with
        | false => exact Or.inl (hpiece.symm.trans he)
        | true => exact Or.inr (Or.inl (hpiece.symm.trans he))
    | spine piece => cases hs
    | tooth owner piece =>
      have he := hpiece.symm.trans (tooth_dart_crossing width height hd hfit owner piece dart.2 hit hs)
      cases hside : dart.2 with
      | false => exact Or.inr (Or.inr (Or.inr (by simpa only [hside, Bool.not_false] using he)))
      | true => exact Or.inr (Or.inr (Or.inl (by simpa only [hside, Bool.not_true] using he)))
  · rintro (rfl | rfl | rfl | rfl)
    · exact crossingDart_vertex width hd hit false
    · exact crossingDart_vertex width hd hit true
    · exact toothCrossingDart_vertex width hd hit false
    · exact toothCrossingDart_vertex width hd hit true

include hfit in
/-- A comb foot has its first tooth dart and precisely those spine neighbors present in the actual array. -/
theorem dart_vertex_foot_iff (dart : Graph.Dart (augmentedGraph width hd)) (vertex : Fin d.1.length) :
    dart.vertex = stationNumber width d (.foot vertex) ↔ dart = toothFootDart width hd vertex ∨
      (∃ hleft, dart = spineLeftDart width hd vertex hleft) ∨
        ∃ hright, dart = spineRightDart width hd vertex hright := by
  constructor
  · intro hv
    have hs := piece_station_of_vertex width hd dart (.foot vertex) hv
    generalize hp : augmentedPiece width hd dart.1 = piece at hs
    have hpiece : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
    cases piece with
    | source edge piece =>
      rcases source_dart_cases width hd edge piece dart.2 with ⟨side, he⟩ | ⟨hit, side, he⟩
      · have ht : edgeTipStation width hd edge side = .foot vertex := by
          apply stationNumber_injective width d
          rw [← sourceTipDart_vertex, ← he, hpiece]
          exact hv
        cases ht
      · have ht : Station.crossing hit = .foot vertex := by
          apply stationNumber_injective width d
          rw [← crossingDart_vertex width hd hit side, ← he, hpiece]
          exact hv
        cases ht
    | spine piece =>
      rcases spine_dart_foot width hd piece dart.2 vertex hs with ⟨hleft, he⟩ | ⟨hright, he⟩
      · exact Or.inr (Or.inl ⟨hleft, hpiece.symm.trans he⟩)
      · exact Or.inr (Or.inr ⟨hright, hpiece.symm.trans he⟩)
    | tooth owner piece =>
      exact Or.inl (hpiece.symm.trans (tooth_dart_foot width height hd hfit owner vertex piece dart.2 hs))
  · rintro (rfl | ⟨hleft, rfl⟩ | ⟨hright, rfl⟩)
    · exact toothFootDart_vertex width hd vertex
    · exact spineLeftDart_vertex width hd vertex hleft
    · exact spineRightDart_vertex width hd vertex hright

end Geometry
end PushPuzzle.PushS.Comb

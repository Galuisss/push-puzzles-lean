/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTourWord
public import PushS.CombUpperPartition
import all PushS.CombStationDarts
import all PushS.CombNativeToothWord
import all PushS.CombToothTour
import all PushS.CombDarts
import all PushS.CombPieces
import all PushS.CombCore
import all PushS.CombUpperVisits
import Mathlib.Algebra.BigOperators.Fin

/-! Complete actual dart inventory of the same literal native comb tour word. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length)

private theorem toothWord_mem_tour (vertex : Fin d.1.length) {dart : Graph.Dart (augmentedGraph width hd)}
    (hm : dart ∈ nativeToothWord width hg drawing hd vertex) : dart ∈ combTourWord width hg drawing hd hv := by
  let index : Fin (d.1.length - 1 + 1) := ⟨(spineRank width d vertex).val, by have := (spineRank width d vertex).isLt; omega⟩
  have hi : tourVertex width d hv index = vertex := by
    unfold tourVertex
    have he : (⟨index.val, by have := index.isLt; omega⟩ : Fin d.1.length) = spineRank width d vertex := Fin.ext rfl
    rw [he, spineVertex_spineRank]
  apply List.mem_append_left
  apply (PushPuzzle.List.mem_blockWalk_iff _ _ _).mpr
  exact Or.inl ⟨index, by rw [hi]; exact hm⟩

private theorem tooth_piece_mem (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool) :
    (Piece.tooth vertex piece).dart width hd side ∈ combTourWord width hg drawing hd hv := by
  apply toothWord_mem_tour width hg drawing hd hv vertex
  cases side with
  | false =>
    apply List.mem_append_left
    apply List.mem_append_left
    exact (PushPuzzle.List.mem_alternatingWalk_iff _ _ _).mpr (Or.inl ⟨piece, rfl⟩)
  | true =>
    apply List.mem_append_right
    apply List.mem_reverse.mpr
    exact (PushPuzzle.List.mem_alternatingWalk_iff _ _ _).mpr (Or.inl ⟨piece, rfl⟩)

private theorem crossing_mem (hit : {c // c ∈ crossings width d}) (side : Bool) :
    crossingDart width hd hit side ∈ combTourWord width hg drawing hd hv := by
  apply toothWord_mem_tour width hg drawing hd hv (.crossing hit : Station width d).tooth
  cases side with
  | false =>
    apply List.mem_append_left
    apply List.mem_append_left
    exact (PushPuzzle.List.mem_alternatingWalk_iff _ _ _).mpr (Or.inr ⟨toothHitIndex width d hit, by rw [toothCrossingHit_index]⟩)
  | true =>
    apply List.mem_append_right
    apply List.mem_reverse.mpr
    exact (PushPuzzle.List.mem_alternatingWalk_iff _ _ _).mpr (Or.inr ⟨toothHitIndex width d hit, by rw [toothCrossingHit_index]⟩)

include hv in
private theorem spine_piece_mem (piece : Fin (d.1.length - 1)) (side : Bool) :
    (Piece.spine piece).dart width hd side ∈ combTourWord width hg drawing hd hv := by
  cases side with
  | false =>
    apply List.mem_append_left
    exact (PushPuzzle.List.mem_blockWalk_iff _ _ _).mpr (Or.inr ⟨piece, rfl⟩)
  | true =>
    apply List.mem_append_right
    exact List.mem_reverse.mpr (List.mem_ofFn.mpr ⟨piece, rfl⟩)

private theorem sum_range (n : ℕ) (f : ℕ → ℕ) :
    ∑ i : Fin n, f i.val = ((List.range n).map f).sum := by
  rw [← List.sum_ofFn]
  congr 1
  apply List.ext_getElem
  · simp
  · intro i hi hj
    simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]

include hd in
private theorem edge_crossing_sum :
    (∑ edge : Fin drawing.incidenceGraph.edges.length, (edgeCrossings width d edge.val).length) = (crossings width d).length := by
  have h := (edgeCrossings_flatMap_perm width d).length_eq
  rw [List.length_flatMap] at h
  rw [sum_range drawing.incidenceGraph.edges.length (fun edge => (edgeCrossings width d edge).length)]
  simpa only [hd.edgeCount] using h

private theorem tooth_crossing_sum :
    (∑ vertex : Fin d.1.length, (toothCrossings width d vertex.val).length) = (crossings width d).length := by
  have hp : ((List.range d.1.length).flatMap (toothCrossings width d)).Perm (crossings width d) := by
    apply (List.Perm.flatMap_left _ (fun vertex _ => toothCrossings_perm width d vertex)).trans
    have he : (crossings width d).filter (fun c => decide (c.vertex < d.1.length)) = crossings width d :=
      List.filter_eq_self.mpr (fun c hc => decide_eq_true (crossing_vertex_lt width d hc))
    simpa only [he] using filter_range_perm Crossing.vertex (crossings width d) d.1.length
  have h := hp.length_eq
  rw [List.length_flatMap] at h
  rw [sum_range d.1.length (fun vertex => (toothCrossings width d vertex).length)]
  exact h

include hg hd in
private theorem native_degree_count : 3 * d.1.length = 2 * drawing.incidenceGraph.edges.length := by
  have hcount : d.1.length = g.vertices.length := by
    rw [hd.vertexCount]
    simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_range]
  have hports (v : NCL.Vertex ℕ) (hv : v ∈ g.vertices) : v.ports.length = 3 := by
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hv
    have h := vertex_isAndOr ⟨g, d⟩ hg i.isLt
    simpa only [List.getD_eq_getElem _ _ i.isLt, List.get_eq_getElem] using h.shape.1
  have hm := (native_tips_perm g hg).length_eq
  have hmap : (g.vertices.map (fun v => v.ports.length)).sum = 3 * g.vertices.length := by
    calc
      _ = (g.vertices.map (fun _ => 3)).sum := by congr 1; exact List.map_congr_left hports
      _ = _ := by simp [Nat.mul_comm]
  simp only [List.length_map, List.length_flatMap, List.length_flatten, List.map_ofFn, Function.comp_def,
    List.length_cons, List.length_nil, List.ofFn_const, List.sum_replicate] at hm
  rw [hmap] at hm
  simpa only [hcount, NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn, smul_eq_mul, Nat.reduceAdd, Nat.mul_comm] using hm

private def tourVertexEquiv : Fin (d.1.length - 1 + 1) ≃ Fin d.1.length where
  toFun := tourVertex width d hv
  invFun vertex := ⟨(spineRank width d vertex).val, by have := (spineRank width d vertex).isLt; omega⟩
  left_inv index := by
    apply Fin.ext
    change (spineRank width d (spineVertex width d ⟨index.val, by have := index.isLt; omega⟩)).val = index.val
    exact congrArg Fin.val (spineRank_spineVertex width d ⟨index.val, by have := index.isLt; omega⟩)
  right_inv vertex := by
    unfold tourVertex
    have he : (⟨(spineRank width d vertex).val, by have := (spineRank width d vertex).isLt; omega⟩ : Fin d.1.length) =
        spineRank width d vertex := Fin.ext rfl
    rw [he, spineVertex_spineRank]

include hv in
private theorem tour_length_count :
    (combTourWord width hg drawing hd hv).length + 2 = 4 * (crossings width d).length + 7 * d.1.length := by
  have hsum := (tourVertexEquiv width hv).sum_comp (fun vertex => (toothCrossings width d vertex.val).length)
  change (∑ index : Fin (d.1.length - 1 + 1), (toothCrossings width d (tourVertex width d hv index).val).length) = _ at hsum
  rw [tooth_crossing_sum width] at hsum
  simp only [combTourWord, List.length_append, combForwardWord, PushPuzzle.List.blockWalk_length,
    combReturnWord, List.length_reverse, List.length_ofFn, nativeToothWord_length]
  simp only [List.sum_ofFn, Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

include hv in
private theorem dart_card_count :
    Fintype.card (Graph.Dart (augmentedGraph width hd)) + 2 =
      4 * (crossings width d).length + 2 * drawing.incidenceGraph.edges.length + 4 * d.1.length := by
  have he := edge_crossing_sum width drawing hd
  have ht := tooth_crossing_sum width (d := d)
  rw [Graph.Dart.card]
  simp only [augmentedGraph, List.length_map, pieces, List.length_append, List.length_flatMap,
    List.length_ofFn]
  simp only [← List.ofFn_eq_map, List.sum_ofFn, Finset.sum_add_distrib,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  omega

include hv in
/-- The complete literal comb word has exactly one occurrence per actual augmented dart in its finite inventory. -/
theorem combTourWord_length : (combTourWord width hg drawing hd hv).length =
    Fintype.card (Graph.Dart (augmentedGraph width hd)) := by
  have hw := tour_length_count width hg drawing hd hv
  have hc := dart_card_count width drawing hd hv
  have hdg := native_degree_count hg drawing hd
  omega

private theorem source_tip_mem (edge : Fin drawing.incidenceGraph.edges.length) (side : Bool) :
    sourceTipDart width hd edge side ∈ combTourWord width hg drawing hd hv := by
  let original : Fin g.edgeCount := ⟨edge.val, by
    simpa only [NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn] using edge.isLt⟩
  let v := if side then drawing.target original else drawing.source original
  have hcount : d.1.length = g.vertices.length := by
    rw [hd.vertexCount]
    simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_range]
  let vertex : Fin d.1.length := ⟨v.val, by simpa only [hcount] using v.isLt⟩
  obtain ⟨weight, hp⟩ := (native_dart_port_iff g hg.1 drawing v original side).mp (by rw [native_dart_vertex]; cases side <;> rfl)
  have hfan : (⟨⟨original.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈ fan width ⟨g, d⟩ vertex.val := by
    apply (fan_perm width ⟨g, d⟩ vertex.val).mem_iff.mpr
    change (⟨⟨original.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈ (g.vertices.getD v.val ⟨[], 0⟩).ports
    simpa only [List.getD_eq_getElem _ _ v.isLt, List.get_eq_getElem] using hp
  obtain ⟨index, hindex⟩ := List.mem_iff_get.mp hfan
  let slot : Fin 3 := ⟨index.val, by rw [← fan_length width ⟨g, d⟩ hg v.isLt]; exact index.isLt⟩
  have hport : nativeFanPort width hg drawing hd vertex slot = (⟨⟨original.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) := hindex
  have hslot : nativeFanDart width hg drawing hd vertex slot = sourceTipDart width hd edge side := by
    apply dartToken_some_injective width hd _ _ (.tip edge.val side)
    · rw [nativeFanDart_token, hport]
      rfl
    · exact sourceTipDart_token width hd edge side
  apply toothWord_mem_tour width hg drawing hd hv vertex
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨slot, hslot⟩))

/-- Every genuine indexed source and comb-tree dart occurs in the same literal actual tour word. -/
theorem combTourWord_cover (dart : Graph.Dart (augmentedGraph width hd)) :
    dart ∈ combTourWord width hg drawing hd hv := by
  generalize hp : augmentedPiece width hd dart.1 = piece
  have he : piece.dart width hd dart.2 = dart := by rw [← hp, Piece.dart_augmentedPiece]
  rw [← he]
  cases piece with
  | source edge piece =>
    rcases source_dart_cases width hd edge piece dart.2 with ⟨side, hs⟩ | ⟨hit, side, hs⟩
    · rw [hs]
      exact source_tip_mem width hg drawing hd hv edge side
    · rw [hs]
      exact crossing_mem width hg drawing hd hv hit side
  | tooth vertex piece => exact tooth_piece_mem width hg drawing hd hv vertex piece dart.2
  | spine piece => exact spine_piece_mem width hg drawing hd hv piece dart.2

/-- Full coverage and the exact actual finite dart inventory make the same literal comb tour duplicate-free. -/
theorem combTourWord_nodup : (combTourWord width hg drawing hd hv).Nodup :=
  PushPuzzle.List.nodup_of_complete_length_le_card _ (combTourWord_cover width hg drawing hd hv)
    (combTourWord_length width hg drawing hd hv).le

end PushPuzzle.PushS.Comb

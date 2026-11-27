/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombContractedReadout
import all PushS.CombContractedReadout
public import PushS.RotationWordNoncrossing
public import PushS.CombUpperNoncrossing
public import CslibFrontier.Foundations.Data.List.IdxOf
import all PushS.CombContraction
import all PushS.CombRetainedTokens
import all PushS.CombNativeFanDarts

/-! Actual native planar drawing, comb tree contraction and original contour readout give source nonalternation. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (hv : 0 < d.1.length)

include hfit in
private theorem contracted_vertex (dart : Graph.Dart (contractedGraph width hd hv)) : dart.vertex = treeRoot width d hv := by
  have he : (contractedGraph width hd hv).edges[dart.1] ∈ (contractedGraph width hd hv).edges := List.getElem_mem dart.1.isLt
  generalize hp : (contractedGraph width hd hv).edges[dart.1] = pair at he
  rw [contractedGraph_eq_root width height hd hfit hv] at he
  obtain ⟨old, _, heq⟩ := List.mem_map.mp he
  have hpair : (contractedGraph width hd hv).edges[dart.1] = (treeRoot width d hv, treeRoot width d hv) := hp.trans heq.symm
  rw [Graph.Dart.edge_eq_vertices dart.1] at hpair
  rcases dart with ⟨edge, side⟩
  cases side
  · exact congrArg Prod.fst hpair
  · exact congrArg Prod.snd hpair

include hfit in
private theorem contracted_word_cover (rotation : Graph.RotationSystem (contractedGraph width hd hv))
    (word : List (Graph.Dart (contractedGraph width hd hv))) (hword : rotation.rotate = word.formPerm)
    (dart : Graph.Dart (contractedGraph width hd hv)) : dart ∈ word := by
  by_contra hnot
  have hfixed : rotation.rotate dart = dart := by rw [hword]; exact List.formPerm_apply_of_notMem hnot
  have hvertex : dart.vertex = dart.reverse.vertex :=
    (contracted_vertex width height hd hfit hv dart).trans (contracted_vertex width height hd hfit hv dart.reverse).symm
  have he := ((rotation.sameCycle_iff dart dart.reverse).mpr hvertex).eq_of_left hfixed
  have hs : dart.2 = !dart.2 := congrArg (fun point : Graph.Dart (contractedGraph width hd hv) => point.2) he
  exact (show ∀ side : Bool, side ≠ !side from by decide) dart.2 hs

end Geometry

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d) (hv : 0 < d.1.length)
  (height : ℕ) (hfit : Graph.drawingFits d width height)
  (hhead : ∀ edge : Fin drawing.incidenceGraph.edges.length,
    (d.2.getD edge []).head? = some (Graph.drawingPosition drawing.incidenceGraph d drawing.incidenceGraph.edges[edge].1))

include drawing hd hv hg hfit hhead in
/-- The same actual native planar source yields nonalternating original source-fragment ends in the emitted contour. -/
theorem sourceNoncrossing_of_native_positive : SourceNoncrossing width ⟨g, d⟩ := by
  obtain ⟨word, hn, hrotation, hread⟩ := contractedRotation_source_word width hg drawing hd hv height hfit hhead
  have hrank (dart : Graph.Dart (contractedGraph width hd hv)) :
      (sourceOrder width ⟨g, d⟩).idxOf (retainedToken width hd hv dart) = word.idxOf dart := by
    rw [← hread]
    exact List.idxOf_map_of_injective (retainedToken_injective width hd hv) word dart
  intro pair hp other hq hcross
  obtain ⟨edge, piece, rfl⟩ := sourcePairs_fragment width hd g hp
  obtain ⟨nextEdge, nextPiece, rfl⟩ := sourcePairs_fragment width hd g hq
  let first := retainedFragmentIndex width hd hv edge piece
  let second := retainedFragmentIndex width hd hv nextEdge nextPiece
  have hsource (edge : Fin drawing.incidenceGraph.edges.length) (piece : Fin ((edgeCrossings width d edge).length + 1)) (side : Bool) :
      (sourceOrder width ⟨g, d⟩).idxOf (fragmentToken width d edge piece side) =
        word.idxOf (retainedFragmentIndex width hd hv edge piece, side) := by
    rw [← retainedToken_fragment width hd hv edge piece side]
    exact hrank _
  simp only [hsource] at hcross
  have hne : first ≠ second := by
    intro he
    change min (word.idxOf (first, false)) (word.idxOf (first, true)) <
      min (word.idxOf (second, false)) (word.idxOf (second, true)) ∧ _ at hcross
    rw [he] at hcross
    omega
  apply contractedRotation_not_alternates width height hd hfit hhead hv first second hne
  apply Graph.RotationSystem.alternates_of_word_crossing _ word hn hrotation
    (contracted_word_cover width height hd hfit hv _ word hrotation _)
    (contracted_word_cover width height hd hfit hv _ word hrotation _)
    (contracted_word_cover width height hd hfit hv _ word hrotation _)
    (contracted_word_cover width height hd hfit hv _ word hrotation _)
  · exact (contracted_vertex width height hd hfit hv _).trans (contracted_vertex width height hd hfit hv _).symm
  · exact (contracted_vertex width height hd hfit hv _).trans (contracted_vertex width height hd hfit hv _).symm
  · exact (contracted_vertex width height hd hfit hv _).trans (contracted_vertex width height hd hfit hv _).symm
  · exact hcross

include drawing hd hg hfit hhead in
/-- Every original valid native planar drawing yields the actual source nonalternation, including the empty drawing. -/
theorem sourceNoncrossing_of_native : SourceNoncrossing width ⟨g, d⟩ := by
  by_cases hpos : 0 < d.1.length
  · exact sourceNoncrossing_of_native_positive width hg drawing hd hpos height hfit hhead
  · have hempty : d.1 = [] := List.eq_nil_of_length_eq_zero (by omega)
    have hedges : d.2.length = g.edgeCount := by
      rw [hd.edgeCount]
      simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn]
    exact sourceNoncrossing_of_drawing_empty width ⟨g, d⟩ hg (native_count drawing hd) hedges hempty

include drawing hd hg hfit hhead in
/-- The actual raw native comb compiler emits a complete valid two-page layout from its original standard planar drawing. -/
theorem compile_pages_valid_of_native : (compile width ⟨g, d⟩).pages.Valid := by
  have hedges : d.2.length = g.edgeCount := by
    rw [hd.edgeCount]
    simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn]
  exact compile_pages_valid_of_sourceNoncrossing width ⟨g, d⟩ hg (native_count drawing hd) hedges
    (sourceNoncrossing_of_native width hg drawing hd height hfit hhead)

end Native
end PushPuzzle.PushS.Comb

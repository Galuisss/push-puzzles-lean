/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTourWord
public import PushS.CombSourceOrder
import all PushS.CombSourceOrder
import all PushS.CombDarts
import all PushS.CombNativeFanDarts
import all PushS.CombPartition
import all PushS.CombOrdering

/-! Reading the actual complete comb tour deletes precisely tree darts and yields the original source contour word. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The original native contour block before inserting its adjacent rotation ears. -/
@[expose] def sourceBlock (width : ℕ) (input : Input) (vertex : ℕ) : List Token :=
  (toothCrossings width input.drawing vertex).map (fun c => c.token false) ++
    (fan width input vertex).map (fun p => incidenceToken p.1) ++
    (toothCrossings width input.drawing vertex).reverse.map (fun c => c.token true)

private theorem core_source_filter (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ)) (hlen : ports.length = 3) :
    (coreTemplate vertex ports).order.filter Token.isSource = ports.map (fun p => incidenceToken p.1) := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  unfold coreTemplate
  extract_lets pa pb pc kind ta tb tc inside outside
  split_ifs <;> rfl

/-- Deleting the original adjacent rotation ears leaves the same native marks and fan slots in order. -/
theorem vertexBlock_source_filter (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph) {vertex : ℕ}
    (hv : vertex < input.graph.vertices.length) :
    (vertexBlock width input vertex).order.filter Token.isSource = sourceBlock width input vertex := by
  simp only [vertexBlock, coreBlock, List.filter_append, core_source_filter vertex (fan width input vertex) (fan_length width input hg hv)]
  simp [sourceBlock, List.filter_map, Crossing.token, Token.isSource, Function.comp_def]

/-- The original source contour consists exactly of the actual native source blocks in their original sorted vertex order. -/
theorem sourceOrder_eq_blocks (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) :
    sourceOrder width input = (vertexOrder width input.drawing).flatMap (fun sv => sourceBlock width input sv.2) := by
  simp only [sourceOrder, cut, List.flatMap_map, List.filter_flatMap]
  apply List.flatMap_congr
  intro site hm
  apply vertexBlock_source_filter width input hg
  have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hm)
  simpa only [prepare, List.length_map, hcount, Nat.add_zero] using hi

private theorem blockWalk_filterMap_none {α β : Type*} {n : ℕ} (blocks : Fin (n + 1) → List α) (bridges : Fin n → α)
    (read : α → Option β) (hnone : ∀ index, read (bridges index) = none) :
    (PushPuzzle.List.blockWalk blocks bridges).filterMap read = (List.ofFn (fun index => (blocks index).filterMap read)).flatten := by
  induction n with
  | zero => simp [PushPuzzle.List.blockWalk, PushPuzzle.List.alternatingWalk]
  | succ n ih =>
    rw [PushPuzzle.List.blockWalk_succ, List.filterMap_append, List.filterMap_cons, hnone 0]
    rw [ih (fun index => blocks index.succ) (fun index => bridges index.succ) (fun index => hnone index.succ)]
    conv_rhs => rw [List.ofFn_succ, List.flatten_cons]

private theorem tourVertex_word (width : ℕ) (d : Graph.OrthogonalDrawing) (hv : 0 < d.1.length) :
    List.ofFn (fun index => (tourVertex width d hv index).val) = (vertexOrder width d).map Prod.snd := by
  apply List.ext_getElem
  · rw [List.length_ofFn, List.length_map, vertexOrder_length]
    omega
  · intro index hi hj
    simp only [List.getElem_ofFn, List.getElem_map, tourVertex, spineVertex, List.get_eq_getElem]

section Geometry

variable (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing} (hd : G.IsPlanarOrthogonalDrawing d)

private theorem tooth_side_readout (vertex : Fin d.1.length) (side : Bool) :
    (PushPuzzle.List.alternatingWalk (fun piece => (Piece.tooth vertex piece).dart width hd side)
      (fun hit => crossingDart width hd (toothCrossingHit width d vertex hit) side)).filterMap (dartToken width hd) =
        (toothCrossings width d vertex).map (fun c => c.token side) := by
  simp only [PushPuzzle.List.alternatingWalk, List.filterMap_cons, Piece.dart_token, Piece.token, List.filterMap_flatten,
    List.map_ofFn, Function.comp_def, List.filterMap_cons, crossingDart_token, List.filterMap_nil]
  change (List.ofFn (fun hit : Fin (toothCrossings width d vertex).length =>
    [(toothCrossingHit width d vertex hit).val.token side])).flatten = _
  calc
    _ = ((List.ofFn fun hit : Fin (toothCrossings width d vertex).length => (toothCrossings width d vertex).get hit).map
        (fun c => [c.token side])).flatten := by rw [List.map_ofFn]; rfl
    _ = _ := by
      rw [List.ofFn_get]
      change (toothCrossings width d vertex).flatMap (fun c => [c.token side]) = _
      exact List.flatMap_pure_eq_map _ _

/-- The actual ascending word reads exactly the original ascending crossing tokens. -/
theorem toothAscent_readout (vertex : Fin d.1.length) :
    (toothAscent width hd vertex).filterMap (dartToken width hd) = (toothCrossings width d vertex).map (fun c => c.token false) :=
  tooth_side_readout width hd vertex false

/-- The actual return word reads exactly the original returning crossing tokens in reverse tooth order. -/
theorem toothDescent_readout (vertex : Fin d.1.length) :
    (toothDescent width hd vertex).filterMap (dartToken width hd) =
      (toothCrossings width d vertex).reverse.map (fun c => c.token true) := by
  rw [toothDescent, List.filterMap_reverse, tooth_side_readout, List.map_reverse]

end Geometry

section Native

variable (width : ℕ) {g : NCL.AndOrGraph} (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)
  {d : Graph.OrthogonalDrawing} (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d)

private theorem native_fan_ofFn (vertex : Fin d.1.length) :
    List.ofFn (nativeFanPort width hg drawing hd vertex) = fan width ⟨g, d⟩ vertex.val := by
  have hv : vertex.val < g.vertices.length := by rw [← native_count drawing hd]; exact vertex.isLt
  apply List.ext_getElem
  · rw [List.length_ofFn, fan_length width ⟨g, d⟩ hg hv]
  · intro index hi hj
    simp only [List.getElem_ofFn, nativeFanPort, List.get_eq_getElem]

/-- Reading the actual three geometric fan darts retains the same original sorted incidence tokens. -/
theorem nativeFan_readout (vertex : Fin d.1.length) :
    (List.ofFn (nativeFanDart width hg drawing hd vertex)).filterMap (dartToken width hd) =
      (fan width ⟨g, d⟩ vertex.val).map (fun p => incidenceToken p.1) := by
  rw [← native_fan_ofFn width hg drawing hd vertex, List.map_ofFn]
  simp only [List.ofFn_succ, List.ofFn_zero, List.filterMap_cons, nativeFanDart_token, List.filterMap_nil, Function.comp_def]

/-- The actual complete tooth word reads exactly its original native source block, preserving every fan and crossing occurrence. -/
theorem nativeToothWord_readout (vertex : Fin d.1.length) :
    (nativeToothWord width hg drawing hd vertex).filterMap (dartToken width hd) = sourceBlock width ⟨g, d⟩ vertex.val := by
  rw [nativeToothWord, List.filterMap_append, List.filterMap_append, toothAscent_readout, nativeFan_readout, toothDescent_readout]
  rfl

/-- Every actual returning spine dart is erased by the original source-token readout. -/
theorem combReturnWord_readout : (combReturnWord width drawing hd).filterMap (dartToken width hd) = [] := by
  rw [combReturnWord, List.filterMap_reverse]
  have hnone : (List.ofFn fun piece => (Piece.spine piece).dart width hd true).filterMap (dartToken width hd) = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro dart hm
    obtain ⟨piece, rfl⟩ := List.mem_ofFn.mp hm
    rw [Piece.dart_token]
    rfl
  rw [hnone, List.reverse_nil]

/-- The actual complete forward comb word reads the original source blocks at precisely its literal native vertex positions. -/
theorem combForwardWord_readout (hv : 0 < d.1.length) :
    (combForwardWord width hg drawing hd hv).filterMap (dartToken width hd) =
      (List.ofFn (fun index => sourceBlock width ⟨g, d⟩ (tourVertex width d hv index).val)).flatten := by
  rw [combForwardWord, blockWalk_filterMap_none]
  · congr 2
    funext index
    exact nativeToothWord_readout width hg drawing hd _
  · intro piece
    rw [Piece.dart_token]
    rfl

/-- Reading the complete actual geometric comb tour yields exactly the original compiled source contour, with all and only auxiliary tree darts erased. -/
theorem combTourWord_readout (hv : 0 < d.1.length) :
    (combTourWord width hg drawing hd hv).filterMap (dartToken width hd) = sourceOrder width ⟨g, d⟩ := by
  rw [combTourWord, List.filterMap_append, combReturnWord_readout, List.append_nil, combForwardWord_readout]
  rw [sourceOrder_eq_blocks width ⟨g, d⟩ hg (native_count drawing hd)]
  calc
    _ = ((List.ofFn fun index => (tourVertex width d hv index).val).map (sourceBlock width ⟨g, d⟩)).flatten := by
      rw [List.map_ofFn]
      rfl
    _ = ((vertexOrder width d).map Prod.snd).flatMap (sourceBlock width ⟨g, d⟩) := by rw [tourVertex_word]; rfl
    _ = _ := by rw [List.flatMap_map]

end Native
end PushPuzzle.PushS.Comb

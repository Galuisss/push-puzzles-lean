/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombAxisPairing
import all PushS.CombAxisPairing
import all PushS.CombNormalizedLocal
import all PushS.CombNormalizedInputs
import all PushS.CombUpperVisits
import all PushS.CombFragmentTokens
import all PushS.CombPartition

/-! Every actual ordinary group retains its original subdivision joint and page parity. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem crossing_pair (width : ℕ) (input : Input)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {c : Crossing}
    (hc : c ∈ crossings width input.drawing) :
    Nonempty (AxisPairAt width input drawing false (c.token false) (c.token true)) := by
  let edge : Fin input.graph.edgeCount := ⟨c.edge, by rw [← hedges]; exact crossing_edge_lt width input.drawing hc⟩
  have hm : c ∈ edgeCrossings width input.drawing edge.val :=
    (edgeCrossings_perm width input.drawing c.edge).mem_iff.mpr (List.mem_filter.mpr ⟨hc, by simp⟩)
  obtain ⟨pre, post, hword⟩ := List.mem_iff_append.mp hm
  let before := endExtension width input drawing edge false ++ [.tip edge.val false] ++ pre.flatMap crossingWord
  let after := post.flatMap crossingWord ++ [.tip edge.val true] ++ endExtension width input drawing edge true
  have hw : axisVisits width input drawing edge = before ++ crossingWord c ++ after := by
    change endExtension width input drawing edge false ++
      ([.tip edge.val false] ++ (edgeCrossings width input.drawing edge.val).flatMap crossingWord ++
        [.tip edge.val true]) ++ endExtension width input drawing edge true = _
    simp only [hword, List.flatMap_append, List.flatMap_cons, before, after, List.append_assoc]
  have hp : before.length % 2 = if false then 0 else 1 := by
    have he := endExtension_even width input drawing edge false
    simp only [before, List.length_append, List.length_cons, List.length_nil, crossingWords_length,
      Bool.false_eq_true, ite_false]
    omega
  cases hf : c.forward with
  | false =>
    have hx := pairAt_of_split width input drawing edge false (c.token true) (c.token false)
      before after (by simpa only [crossingWord, hf, Bool.false_eq_true, ite_false] using hw) hp
    exact hx.map AxisPairAt.swap
  | true =>
    exact pairAt_of_split width input drawing edge false (c.token false) (c.token true)
      before after (by simpa only [crossingWord, hf, ite_true] using hw) hp

private theorem rotation_wire_pair (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) {port : NCL.Port ℕ} {weight : ℕ}
    (hp : (.rotation vertex.val true, ⟨port, weight⟩) ∈ (coreBlock width input vertex.val).core.ports) :
    Nonempty (AxisPairAt width input drawing false (.rotation vertex.val false) (incidenceToken port)) := by
  obtain ⟨edge, he, hv, ht⟩ := coreRotation_end width input hg drawing vertex hp
  have hx := endExtension_of_rotation width input drawing edge port.dir vertex hv ht
  cases hs : port.dir with
  | false =>
    simp only [hs, Bool.false_eq_true, ite_false] at hx
    apply pairAt_of_split width input drawing edge false _ _ [.rotation vertex.val true]
      ((edgeCrossings width input.drawing edge.val).flatMap crossingWord ++ [.tip edge.val true] ++
        endExtension width input drawing edge true)
    · simp only [axisVisits, hx, edgeVisits, List.cons_append, List.nil_append,
        List.append_assoc, incidenceToken, hs, he]
      rfl
    · rfl
  | true =>
    simp only [hs, ite_true] at hx
    have hw := pairAt_of_split width input drawing edge false (incidenceToken port) (.rotation vertex.val false)
      (endExtension width input drawing edge false ++ [.tip edge.val false] ++
        (edgeCrossings width input.drawing edge.val).flatMap crossingWord) [.rotation vertex.val true]
      (by simp only [axisVisits, hx, edgeVisits, List.cons_append, List.nil_append,
        List.append_assoc, incidenceToken, hs, he]; rfl) (by
        have ha := endExtension_even width input drawing edge false
        simp only [List.length_append, List.length_cons, List.length_nil, crossingWords_length,
          Bool.false_eq_true, ite_false]
        omega)
    exact hw.map AxisPairAt.swap

private theorem core_wire_pair (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) {a b : Token}
    (hw : .wire a b ∈ (coreBlock width input vertex.val).lower) :
    Nonempty (AxisPairAt width input drawing false a b) := by
  obtain ⟨port, weight, he, hp, _⟩ := core_wire_spec width input hg vertex.isLt hw
  have hx := rotation_wire_pair width input hg drawing vertex hp
  rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hx.map AxisPairAt.swap
  · exact hx

/-- Each actual upper pair is one even joint of the same original native subdivision. -/
theorem upperPair_axisPairAt (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {a b : Token}
    (hu : (a, b) ∈ (cut width input).upper) :
    Nonempty (AxisPairAt width input drawing true a b) := by
  rcases List.mem_append.mp hu with hfragment | hrotation
  · obtain ⟨re, hre, hp⟩ := List.mem_flatMap.mp hfragment
    have he : re.2 < input.graph.edgeCount := by
      rw [← hedges]
      simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hre
    exact upperFragment_axisPairAt width input drawing ⟨re.2, he⟩ hp
  · obtain ⟨block, hblock, hu⟩ := List.mem_flatMap.mp hrotation
    obtain ⟨sv, hsv, rfl⟩ := List.mem_map.mp hblock
    have hv := vertex_bound width input hcount hsv
    exact upperRotation_axisPairAt width input hg drawing ⟨sv.2, hv⟩ hu

/-- Each actual lower ordinary WIRE is one odd joint of the same original native subdivision. -/
theorem lowerWire_axisPairAt (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {a b : Token}
    (hw : .wire a b ∈ (cut width input).lower) :
    Nonempty (AxisPairAt width input drawing false a b) := by
  obtain ⟨vertex, hv, hw⟩ := lower_owner width input hcount hw
  rcases List.mem_append.mp hw with hcross | hcore
  · obtain ⟨c, hc, he⟩ := List.mem_map.mp hcross
    cases he
    exact crossing_pair width input hedges drawing (tooth_mem width input.drawing hc).1
  · exact core_wire_pair width input hg drawing ⟨vertex, hv⟩ hcore

end PushPuzzle.PushS.Comb

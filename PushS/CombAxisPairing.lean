/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionCores
import all PushS.CombAxisVisits
import all PushS.CombUpperVisits
import all PushS.CombNormalizedLocal
import all PushS.CombAxisInventory

/-! Actual upper and lower ordinary wires are consecutive joints of the original native subdivision. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL.ConstraintGraph

/-- One actual ordinary pair is one joint of the same original standard subdivision. -/
structure AxisPairAt (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (upper : Bool) (a b : Token) where
  /-- The original edge and its actual consecutive axis position. -/
  joint : Subdivision.Joint (axisJointCount width input drawing)
  /-- The same literal endpoints, allowing the emitted pair's local order. -/
  ends :
    (segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = a ∧
      segmentToken width input drawing ⟨joint.1, joint.2.succ⟩ = b) ∨
    (segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = b ∧
      segmentToken width input drawing ⟨joint.1, joint.2.succ⟩ = a)
  /-- Actual upper joints start at even positions; lower joints start at odd positions. -/
  parity : joint.2.val % 2 = if upper then 0 else 1

private theorem pairAt_of_split (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount)
    (upper : Bool) (a b : Token) (before after : List Token)
    (hw : axisVisits width input drawing edge = before ++ [a, b] ++ after)
    (hp : before.length % 2 = if upper then 0 else 1) :
    Nonempty (AxisPairAt width input drawing upper a b) := by
  have hl := congrArg List.length hw
  simp only [List.length_append, List.length_cons, List.length_nil] at hl
  have hj : before.length < axisJointCount width input drawing edge := by
    simp only [axisJointCount]
    omega
  let joint : Subdivision.Joint (axisJointCount width input drawing) := ⟨edge, ⟨before.length, hj⟩⟩
  refine ⟨⟨joint, Or.inl ⟨?_, ?_⟩, hp⟩⟩
  all_goals simp only [segmentToken, List.get_eq_getElem, joint, Fin.val_castSucc, Fin.val_succ]
  all_goals simp [hw]

private def AxisPairAt.swap {width : ℕ} {input : Input}
    {drawing : NCL.GridDrawing.Closed input.graph.graph} {upper : Bool} {a b : Token}
    (p : AxisPairAt width input drawing upper a b) : AxisPairAt width input drawing upper b a :=
  ⟨p.joint, p.ends.symm, p.parity⟩

private theorem pairOff_split (tokens : List Token) (he : tokens.length % 2 = 0)
    {a b : Token} (hp : (a, b) ∈ pairOff tokens) :
    ∃ before after, tokens = before ++ [a, b] ++ after ∧ before.length % 2 = 0 := by
  induction tokens using List.twoStepInduction with
  | nil => simp only [pairOff, List.zipIdx_nil, List.filterMap_nil, List.not_mem_nil] at hp
  | singleton t => simp at he
  | cons_cons x y tail ih =>
    rw [pairOff_cons_cons] at hp
    rcases List.mem_cons.mp hp with heq | hp
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
      exact ⟨[], tail, rfl, rfl⟩
    · obtain ⟨before, after, hw, hpar⟩ := ih (by simp only [List.length_cons] at he; omega) hp
      refine ⟨x :: y :: before, after, by simp only [hw, List.cons_append], ?_⟩
      simp only [List.length_cons]
      omega

private theorem endExtension_even (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) (side : Bool) :
    (endExtension width input drawing edge side).length % 2 = 0 := by
  rcases endExtension_length width input drawing edge side with h | h <;> omega

/-- Every actual original-edge upper fragment is one even native subdivision joint. -/
theorem upperFragment_axisPairAt (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount)
    {a b : Token} (hp : (a, b) ∈ pairOff (edgeVisits width input.drawing edge.val)) :
    Nonempty (AxisPairAt width input drawing true a b) := by
  obtain ⟨before, after, hw, he⟩ := pairOff_split _ (edgeVisits_length_even width input.drawing edge.val) hp
  apply pairAt_of_split width input drawing edge true a b
    (endExtension width input drawing edge false ++ before)
    (after ++ endExtension width input drawing edge true)
  · simp only [axisVisits, hw, List.append_assoc]
  · have hp := endExtension_even width input drawing edge false
    simp only [List.length_append, ite_true]
    omega

private theorem rotation_pair (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length)
    {port : NCL.Port ℕ} {weight : ℕ}
    (hp : (.rotation vertex.val true, ⟨port, weight⟩) ∈ (coreBlock width input vertex.val).core.ports) :
    Nonempty (AxisPairAt width input drawing true (.rotation vertex.val true) (.rotation vertex.val false)) := by
  obtain ⟨edge, _, hv, ht⟩ := coreRotation_end width input hg drawing vertex hp
  have hx := endExtension_of_rotation width input drawing edge port.dir vertex hv ht
  cases hs : port.dir with
  | false =>
    simp only [hs, Bool.false_eq_true, ite_false] at hx
    exact pairAt_of_split width input drawing edge true _ _ []
      (edgeVisits width input.drawing edge.val ++ endExtension width input drawing edge true)
      (by simp only [axisVisits, hx, List.nil_append, List.append_assoc]) rfl
  | true =>
    simp only [hs, ite_true] at hx
    have hw := pairAt_of_split width input drawing edge true
      (.rotation vertex.val false) (.rotation vertex.val true)
      (endExtension width input drawing edge false ++ edgeVisits width input.drawing edge.val) []
      (by simp only [axisVisits, hx, List.append_nil]) (by
        have ha := endExtension_even width input drawing edge false
        have hb := edgeVisits_length_even width input.drawing edge.val
        simp only [List.length_append, ite_true]
        omega)
    exact hw.map AxisPairAt.swap

/-- Every actual local upper rotation is one even native subdivision joint. -/
theorem upperRotation_axisPairAt (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) {a b : Token}
    (hu : (a, b) ∈ (vertexBlock width input vertex.val).upper) :
    Nonempty (AxisPairAt width input drawing true a b) := by
  have hm : .rotation vertex.val true ∈ (coreBlock width input vertex.val).order := by
    have hp := core_order_perm vertex.val (fan width input vertex.val) (fan_length width input hg vertex.isLt)
    apply hp.mem_iff.mpr
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨(a, b), hu, ?_⟩
    rcases vertexBlock_upper_shape width input vertex.val hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pairTokens]
  obtain ⟨port, weight, hp⟩ := (coreTemplate_rotation_mem vertex.val (fan width input vertex.val) true).mp hm
  have hx := rotation_pair width input hg drawing vertex hp
  rcases vertexBlock_upper_shape width input vertex.val hu with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hx
  · exact hx.map AxisPairAt.swap

end PushPuzzle.PushS.Comb

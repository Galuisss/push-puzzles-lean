/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombAxisLowerPairing
import all PushS.CombNormalizedInputs
import all PushS.CombNormalizedLocal

/-! Actual page ownership recovers every original standard subdivision joint. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL.ConstraintGraph

/-- The standard joint at a real ordinary group is exactly its actual page-supply constraint.
-/
theorem AxisPairAt.sat_iff {width : ℕ} {input : Input}
    {drawing : NCL.GridDrawing.Closed input.graph.graph} {upper : Bool} {a b : Token}
    (pair : AxisPairAt width input drawing upper a b) (direction : Token → Bool) :
    (axisGraph width input drawing (.inr pair.joint)).Sat (direction ∘ segmentToken width input drawing) ↔
      direction a = upper ∨ direction b = upper := by
  have hleft : axisParity width input drawing ⟨pair.joint.1, pair.joint.2.castSucc⟩ = !upper := by
    cases upper <;> simp [axisParity, pair.parity]
  have hright : axisParity width input drawing ⟨pair.joint.1, pair.joint.2.succ⟩ = upper := by
    cases upper <;> simp [axisParity, Nat.add_mod, pair.parity]
  simp only [axisGraph, reorient, Subdivision.graph, NCL.Vertex.reorient, NCL.Vertex.Sat, NCL.Vertex.inflow]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
    NCL.WeightedPort.reorient, NCL.Port.In, NCL.Port.reorient, Function.comp_apply, hleft, hright]
  rcases pair.ends with ⟨ha, hb⟩ | ⟨ha, hb⟩
  all_goals simp only [ha, hb]
  all_goals cases upper <;> cases direction a <;> cases direction b <;> decide

private theorem jointFirst_injective {E : Type} (n : E → ℕ) :
    Function.Injective (fun j : Subdivision.Joint n => (⟨j.1, j.2.castSucc⟩ : Subdivision.Segment n)) := by
  rintro ⟨e, a⟩ ⟨f, b⟩ he
  have hef : e = f := congrArg Sigma.fst he
  subst f
  have hab : a.val = b.val := congrArg (fun s : Subdivision.Segment n => s.2.val) he
  exact congrArg (Sigma.mk e) (Fin.ext hab)

private theorem pairJoint_eq {width : ℕ} {input : Input} (hg : NCL.SourceValid input.graph)
    {drawing : NCL.GridDrawing.Closed input.graph.graph} {upper : Bool} {a b : Token}
    (pair : AxisPairAt width input drawing upper a b)
    (joint : Subdivision.Joint (axisJointCount width input drawing))
    (hpar : joint.2.val % 2 = pair.joint.2.val % 2)
    (hm : segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = a ∨
      segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = b) : joint = pair.joint := by
  have hsame {token : Token} (ht : segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = token)
      (hp : segmentToken width input drawing ⟨pair.joint.1, pair.joint.2.castSucc⟩ = token) : joint = pair.joint :=
    jointFirst_injective _ (segmentToken_injective width input hg drawing (ht.trans hp.symm))
  have hnext {token : Token} (ht : segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ = token)
      (hp : segmentToken width input drawing ⟨pair.joint.1, pair.joint.2.succ⟩ = token) : False := by
    have he := segmentToken_injective width input hg drawing (ht.trans hp.symm)
    have hi := congrArg (fun s : Subdivision.Segment (axisJointCount width input drawing) => s.2.val) he
    change joint.2.val = pair.joint.2.val + 1 at hi
    omega
  rcases pair.ends with ⟨ha, hb⟩ | ⟨ha, hb⟩ <;> rcases hm with ht | ht
  · exact hsame ht ha
  · exact False.elim (hnext ht hb)
  · exact False.elim (hnext ht hb)
  · exact hsame ht ha

private theorem lowerGate_endpoint (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {kind : Shuttle.Kind} {a b c token : Token}
    (hgate : .gate kind a b c ∈ (cut width input).lower) (ht : token ∈ [a, b, c]) :
    ∃ edge : Fin input.graph.edgeCount, token = endToken width input drawing edge false ∨
      token = endToken width input drawing edge true := by
  obtain ⟨vertex, hv, hgate⟩ := lower_owner width input hcount hgate
  obtain ⟨_, hp⟩ := vertexBlock_gate_metadata width input vertex hgate
  have hm : token ∈ (coreBlock width input vertex).core.ports.map Prod.fst := hp ▸ ht
  obtain ⟨⟨_, port, weight⟩, hp, rfl⟩ := List.mem_map.mp hm
  obtain ⟨edge, _, _, he⟩ := corePort_end width input hg drawing ⟨vertex, hv⟩ hp
  refine ⟨edge, ?_⟩
  cases hs : port.dir with
  | false => exact Or.inl (hs ▸ he.symm)
  | true => exact Or.inr (hs ▸ he.symm)

private theorem joint_token_not_gate (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (joint : Subdivision.Joint (axisJointCount width input drawing)) (hodd : joint.2.val % 2 = 1)
    {kind : Shuttle.Kind} {a b c : Token}
    (hgate : .gate kind a b c ∈ (cut width input).lower)
    (ht : segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩ ∈ [a, b, c]) : False := by
  obtain ⟨edge, he | he⟩ := lowerGate_endpoint width input hg hcount drawing hgate ht
  · rw [← segmentToken_first width input hg drawing edge] at he
    have hs := segmentToken_injective width input hg drawing he
    have hi := congrArg (fun s : Subdivision.Segment (axisJointCount width input drawing) => s.2.val) hs
    change joint.2.val = 0 at hi
    omega
  · rw [← segmentToken_last width input hg drawing edge] at he
    have hs := segmentToken_injective width input hg drawing he
    have hedge := congrArg Sigma.fst hs
    have hi := congrArg (fun s : Subdivision.Segment (axisJointCount width input drawing) => s.2.val) hs
    change joint.2.val = axisJointCount width input drawing edge at hi
    have hj := joint.2.isLt
    have hsize : axisJointCount width input drawing joint.1 = axisJointCount width input drawing edge :=
      congrArg (axisJointCount width input drawing) hedge
    omega

private theorem joint_actual_pair (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (joint : Subdivision.Joint (axisJointCount width input drawing)) :
    (∃ a b, (a, b) ∈ (cut width input).upper ∧
      ∃ pair : AxisPairAt width input drawing true a b, joint = pair.joint) ∨
    (∃ a b, .wire a b ∈ (cut width input).lower ∧
      ∃ pair : AxisPairAt width input drawing false a b, joint = pair.joint) := by
  let token := segmentToken width input drawing ⟨joint.1, joint.2.castSucc⟩
  have ht : token ∈ (cut width input).order := axisVisits_mem_cut width input hg hcount hedges drawing _
    (segmentToken_mem width input drawing _)
  by_cases hpar : joint.2.val % 2 = 0
  · obtain ⟨index, hm, _⟩ := cut_upper_unique width input hg hcount hedges ht
    let pair := (cut width input).upper.get index
    obtain ⟨location⟩ := upperPair_axisPairAt width input hg hcount hedges drawing (List.get_mem _ index)
    exact Or.inl ⟨pair.1, pair.2, List.get_mem _ index, location,
      pairJoint_eq hg location joint (by rw [location.parity]; exact hpar) hm⟩
  · have hodd : joint.2.val % 2 = 1 := by omega
    obtain ⟨index, hm, _⟩ := cut_lower_unique width input hg hcount ht
    have hgroup := List.get_mem (cut width input).lower index
    cases hg' : (cut width input).lower.get index with
    | wire a b =>
      rw [hg'] at hgroup hm
      obtain ⟨location⟩ := lowerWire_axisPairAt width input hg hcount hedges drawing hgroup
      exact Or.inr ⟨a, b, hgroup, location, pairJoint_eq hg location joint
        (by rw [location.parity]; exact hodd) (by simpa only [TokenGroup.tokens, List.mem_cons,
          List.not_mem_nil, or_false] using hm)⟩
    | gate kind a b c =>
      rw [hg'] at hgroup hm
      exact False.elim (joint_token_not_gate width input hg hcount drawing joint hodd hgroup hm)

/-- All original native subdivision joints are exactly the real upper and lower ordinary constraints.
-/
theorem axisGraph_joints_sat_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (direction : Token → Bool) :
    (∀ joint, (axisGraph width input drawing (.inr joint)).Sat
      (direction ∘ segmentToken width input drawing)) ↔
      (∀ a b, (a, b) ∈ (cut width input).upper → direction a = true ∨ direction b = true) ∧
      (∀ a b, .wire a b ∈ (cut width input).lower → direction a = false ∨ direction b = false) := by
  constructor
  · intro h
    constructor
    · intro a b hp
      obtain ⟨pair⟩ := upperPair_axisPairAt width input hg hcount hedges drawing hp
      exact (pair.sat_iff direction).mp (h pair.joint)
    · intro a b hp
      obtain ⟨pair⟩ := lowerWire_axisPairAt width input hg hcount hedges drawing hp
      exact (pair.sat_iff direction).mp (h pair.joint)
  · rintro ⟨hu, hl⟩ joint
    rcases joint_actual_pair width input hg hcount hedges drawing joint with
      ⟨a, b, hp, pair, rfl⟩ | ⟨a, b, hp, pair, rfl⟩
    · exact (pair.sat_iff direction).mpr (hu a b hp)
    · exact (pair.sat_iff direction).mpr (hl a b hp)

end PushPuzzle.PushS.Comb

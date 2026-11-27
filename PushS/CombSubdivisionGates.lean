/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionJoints
import all PushS.CombNormalizedLocal
import all PushS.CombNormalizedInputs

/-! The original native core constraints are exactly the same actual labelled lower triples. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The actual lower triple of an original native core retains its exact standard gate constraint.
-/
theorem axisGraph_gate_sat_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) (direction : Token → Bool)
    {kind : Shuttle.Kind} {a b c : Token}
    (hgate : .gate kind a b c ∈ (vertexBlock width input vertex.val).lower) :
    (axisGraph width input drawing (.inl vertex)).Sat (direction ∘ segmentToken width input drawing) ↔
      match kind with
      | .andGate => direction c = false ∨ (direction a = false ∧ direction b = false)
      | .orGate => direction a = false ∨ direction b = false ∨ direction c = false := by
  obtain ⟨hk, ht⟩ := vertexBlock_gate_metadata width input vertex.val hgate
  rw [axisGraph_core_sat_iff width input hg drawing vertex direction]
  rcases coreBlock_weights width input hg vertex.isLt with ⟨hkind, hw⟩ | ⟨hkind, hw⟩
  all_goals have hkind' := hk.symm.trans hkind
  all_goals cases hkind'
  all_goals obtain ⟨p, r, s, hp⟩ := ports_of_tokens_weights ht hw
  all_goals simp only [hp, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero]
  all_goals cases direction a <;> cases direction b <;> cases direction c <;> decide

private theorem vertexBlock_lower_mem (width : ℕ) (input : Input)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (vertex : Fin input.graph.vertices.length) {group : TokenGroup}
    (hg : group ∈ (vertexBlock width input vertex.val).lower) : group ∈ (cut width input).lower := by
  have hi : vertex.val < (prepare width input.drawing).1.length := by
    simpa only [prepare, List.length_map, hcount] using vertex.isLt
  let point := (prepare width input.drawing).1[vertex.val]
  have hm : (point, vertex.val) ∈ vertexOrder width input.drawing :=
    (vertexOrder_perm width input.drawing).mem_iff.mpr
      (List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi))
  exact List.mem_flatMap.mpr ⟨_, List.mem_map.mpr ⟨_, hm, rfl⟩, hg⟩

/-- All original native cores are exactly the actual AND and OR gate constraints. -/
theorem axisGraph_cores_sat_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (direction : Token → Bool) :
    (∀ vertex, (axisGraph width input drawing (.inl vertex)).Sat
      (direction ∘ segmentToken width input drawing)) ↔
      (∀ a b c, .gate .andGate a b c ∈ (cut width input).lower →
        direction c = false ∨ (direction a = false ∧ direction b = false)) ∧
      (∀ a b c, .gate .orGate a b c ∈ (cut width input).lower →
        direction a = false ∨ direction b = false ∨ direction c = false) := by
  constructor
  · intro h
    constructor
    all_goals intro a b c hgate
    all_goals obtain ⟨vertex, hv, hgate⟩ := lower_owner width input hcount hgate
    all_goals exact (axisGraph_gate_sat_iff width input hg drawing ⟨vertex, hv⟩ direction hgate).mp (h _)
  · rintro ⟨ha, ho⟩ vertex
    obtain ⟨a, b, c, _, hgate⟩ := vertexBlock_core_group width input vertex.val
    have hglobal := vertexBlock_lower_mem width input hcount vertex hgate
    cases hk : (vertexBlock width input vertex.val).core.kind with
    | andGate =>
      exact (axisGraph_gate_sat_iff width input hg drawing vertex direction (hk ▸ hgate)).mpr
        (ha a b c (hk ▸ hglobal))
    | orGate =>
      exact (axisGraph_gate_sat_iff width input hg drawing vertex direction (hk ▸ hgate)).mpr
        (ho a b c (hk ▸ hglobal))

end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombAxisVisits
public import PushS.CombUpperPartition
import all PushS.CombAxisVisits
import all PushS.CombUpperPartition
import all PushS.CombPartition
import all PushS.CombNormalizedLocal

/-! The actual original-edge chains partition the complete emitted axis inventory. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem core_order_mem_cut (width : ℕ) (input : Input)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (vertex : Fin input.graph.vertices.length) {token : Token}
    (ht : token ∈ (coreBlock width input vertex.val).order) : token ∈ (cut width input).order := by
  have hi : vertex.val < (prepare width input.drawing).1.length := by
    simpa only [prepare, List.length_map, hcount] using vertex.isLt
  let point := (prepare width input.drawing).1[vertex.val]
  have hp : (point, vertex.val) ∈ (prepare width input.drawing).1.zipIdx :=
    List.mem_zipIdx_iff_getElem?.mpr (List.getElem?_eq_getElem hi)
  apply List.mem_flatMap.mpr
  refine ⟨vertexBlock width input vertex.val,
    List.mem_map.mpr ⟨(point, vertex.val), (vertexOrder_perm width input.drawing).mem_iff.mpr hp, rfl⟩, ?_⟩
  exact List.mem_append_left _ (List.mem_append_right _ ht)

private theorem visits_mem_cut (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (edge : Fin input.graph.edgeCount) {token : Token}
    (ht : token ∈ edgeVisits width input.drawing edge.val) : token ∈ (cut width input).order := by
  have he : edge.val ∈ List.range input.drawing.2.length := List.mem_range.mpr (by rw [hedges]; exact edge.isLt)
  have hm := (allEdgeVisits_perm width input hg hedges).mem_iff.mp
    (List.mem_flatMap.mpr ⟨edge.val, he, ht⟩)
  exact (cut_order_perm width input hg hcount).mem_iff.mpr (List.mem_append_left _ hm)

private theorem extension_mem_cut (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) {token : Token}
    (ht : token ∈ endExtension width input drawing edge side) : token ∈ (cut width input).order := by
  obtain ⟨b, rfl⟩ := endExtension_mem width input drawing edge side ht
  obtain ⟨weight, hp⟩ := endVertex_port input hg drawing edge side
  have hc := corePortToken_spec width input hg _ hp
  rw [← endToken, extension_endToken width input hg drawing edge side ht] at hc
  apply core_order_mem_cut width input hcount (endVertex input drawing edge side)
  exact (coreTemplate_rotation_mem _ _ b).mpr ⟨_, _, hc⟩

/-- Every actual original-edge axis belongs to the same emitted contour. -/
theorem axisVisits_mem_cut (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) {token : Token}
    (ht : token ∈ axisVisits width input drawing edge) : token ∈ (cut width input).order := by
  rcases List.mem_append.mp ht with ht | ht
  · rcases List.mem_append.mp ht with ht | ht
    · exact extension_mem_cut width input hg hcount drawing edge false ht
    · exact visits_mem_cut width input hg hcount hedges edge ht
  · exact extension_mem_cut width input hg hcount drawing edge true ht

private theorem rotation_mem_axisVisits (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) (side : Bool)
    (ht : .rotation vertex.val side ∈ (coreBlock width input vertex.val).order) :
    ∃ edge : Fin input.graph.edgeCount, .rotation vertex.val side ∈ axisVisits width input drawing edge := by
  obtain ⟨port, weight, hp⟩ := (coreTemplate_rotation_mem vertex.val (fan width input vertex.val) side).mp ht
  obtain ⟨edge, _, hv, hend⟩ := coreRotation_end width input hg drawing vertex hp
  have hm : .rotation vertex.val side ∈ endExtension width input drawing edge port.dir := by
    simp only [endExtension, hend, reduceCtorEq, ite_false, hv]
    cases port.dir <;> cases side <;> simp
  refine ⟨edge, ?_⟩
  cases hside : port.dir with
  | false => exact List.mem_append_left _ (List.mem_append_left _ (hside ▸ hm))
  | true => exact List.mem_append_right _ (hside ▸ hm)

/-- Every emitted axis is on one of the actual original-edge chains. -/
theorem exists_axisVisits (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {token : Token}
    (ht : token ∈ (cut width input).order) :
    ∃ edge : Fin input.graph.edgeCount, token ∈ axisVisits width input drawing edge := by
  have hp := (cut_order_perm width input hg hcount).mem_iff.mp ht
  rcases List.mem_append.mp hp with hp | hp
  · rcases List.mem_append.mp hp with hp | hp
    · have hr := (nativeTips_perm_range input hg).mem_iff.mp hp
      obtain ⟨edge, he, ht⟩ := List.mem_flatMap.mp hr
      refine ⟨⟨edge, List.mem_range.mp he⟩, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      exact (edgeVisits_mem width input.drawing edge token).mpr (ht.imp_right Or.inl)
    · obtain ⟨c, hc, ht⟩ := List.mem_flatMap.mp hp
      have he : c.edge < input.graph.edgeCount := hedges ▸ crossing_edge_lt width input.drawing hc
      refine ⟨⟨c.edge, he⟩, List.mem_append_left _ (List.mem_append_right _ ?_)⟩
      exact (edgeVisits_mem width input.drawing c.edge token).mpr (.inr (.inr ⟨c, hc, rfl, by
        simpa only [markSides, List.mem_cons, List.not_mem_nil, or_false] using ht⟩))
  · obtain ⟨sv, hsv, ht⟩ := List.mem_flatMap.mp hp
    obtain ⟨pair, hpair, ht⟩ := List.mem_flatMap.mp ht
    have hv : sv.2 < input.graph.vertices.length := by
      have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hsv)
      simpa only [prepare, List.length_map, hcount, Nat.add_zero] using hi
    have hm : token ∈ (coreBlock width input sv.2).order := by
      exact (core_order_perm _ _ (fan_length width input hg hv)).mem_iff.mpr
        (List.mem_append_right _ (List.mem_flatMap.mpr ⟨pair, hpair, ht⟩))
    rcases (vertexBlock_upper_shape width input sv.2 hpair) with ⟨ha, hb⟩ | ⟨ha, hb⟩
    all_goals simp only [pairTokens, List.mem_cons, List.not_mem_nil, or_false, ha, hb] at ht
    all_goals rcases ht with rfl | rfl
    all_goals exact rotation_mem_axisVisits width input hg drawing ⟨sv.2, hv⟩ _ hm

/-- Each actual contour axis belongs to exactly one original native edge chain. -/
theorem axisVisits_partition (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) {token : Token}
    (ht : token ∈ (cut width input).order) :
    ∃! edge : Fin input.graph.edgeCount, token ∈ axisVisits width input drawing edge := by
  obtain ⟨edge, he⟩ := exists_axisVisits width input hg hcount hedges drawing ht
  refine ⟨edge, he, ?_⟩
  intro other ho
  by_contra hne
  exact List.disjoint_left.mp (axisVisits_disjoint width input hg drawing hne) ho he

end PushPuzzle.PushS.Comb

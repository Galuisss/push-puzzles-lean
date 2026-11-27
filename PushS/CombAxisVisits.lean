/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCoreIncidences
public import PushS.CombNativeIncidence
public import PushS.CombFragmentTokens
public import PushS.CombConfigurationCore
import all PushS.CombFragmentTokens

/-!
# The actual axis chain replacing each original native edge

The original edge visits are extended through the literal inside/outside rotation at either
native endpoint. The same standard closed drawing locates the endpoints in the original graph.
-/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The original native vertex at the specified reference end of the drawn edge. -/
@[expose] def endVertex (input : Input) (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) : Fin input.graph.vertices.length :=
  if side then drawing.target edge else drawing.source edge

private theorem endVertex_port (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount)
    (side : Bool) :
    ∃ weight, (⟨⟨edge.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈
      (input.graph.vertices.get (endVertex input drawing edge side)).ports := by
  apply (native_dart_port_iff input.graph hg.1 drawing _ edge side).mp
  rw [native_dart_vertex]
  cases side <;> rfl

/-- The actual core axis retaining this same original native incidence. -/
@[expose] def endToken (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) : Token :=
  (coreBlock width input (endVertex input drawing edge side).val).core.portToken ⟨edge.val, side⟩

/-- Each native endpoint is carried by its own actual direct tip or inside-rotation axis. -/
theorem endToken_role (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount)
    (side : Bool) :
    endToken width input drawing edge side = .tip edge.val side ∨
      endToken width input drawing edge side =
        .rotation (endVertex input drawing edge side).val true := by
  obtain ⟨weight, hp⟩ := endVertex_port input hg drawing edge side
  exact corePortToken_role width input hg _ hp

/-- The actual native core axes retain both the original edge and its endpoint tag. -/
theorem endToken_injective (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (left right : Fin input.graph.edgeCount) (s t : Bool)
    (he : endToken width input drawing left s = endToken width input drawing right t) :
    left = right ∧ s = t := by
  rcases endToken_role width input hg drawing left s with hl | hl <;>
    rcases endToken_role width input hg drawing right t with hr | hr
  · have hp := Token.tip.inj (hl.symm.trans (he.trans hr))
    exact ⟨Fin.ext hp.1, hp.2⟩
  · cases hl.symm.trans (he.trans hr)
  · cases hl.symm.trans (he.trans hr)
  · have hv := (Token.rotation.inj (hl.symm.trans (he.trans hr))).1
    have hv' : endVertex input drawing left s = endVertex input drawing right t := Fin.ext hv
    obtain ⟨a, ha⟩ := endVertex_port input hg drawing left s
    obtain ⟨b, hb⟩ := endVertex_port input hg drawing right t
    rw [← hv'] at hb
    have he' := he
    simp only [endToken, ← hv'] at he'
    have hp := corePortToken_injective width input hg _ ha hb he'
    exact ⟨Fin.ext (congrArg NCL.Port.edge hp), congrArg NCL.Port.dir hp⟩

/-- Every actual core metadata token retains its precise original edge, endpoint tag, and native vertex. -/
theorem corePort_end (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) {token : Token} {port : NCL.Port ℕ} {weight : ℕ}
    (hp : (token, ⟨port, weight⟩) ∈ (coreBlock width input vertex.val).core.ports) :
    ∃ edge : Fin input.graph.edgeCount, edge.val = port.edge ∧
      endVertex input drawing edge port.dir = vertex ∧
      endToken width input drawing edge port.dir = token := by
  have horig : (⟨port, weight⟩ : NCL.WeightedPort ℕ) ∈ (input.graph.vertices.get vertex).ports := by
    have hp' := (coreBlock_ports_perm width input hg vertex.isLt).mem_iff.mp (List.mem_map.mpr ⟨_, hp, rfl⟩)
    simpa only [List.getD_eq_get _ _ vertex] using hp'
  let edge : Fin input.graph.edgeCount := ⟨port.edge, hg.1 _ (List.get_mem _ vertex) _ horig⟩
  have hv : endVertex input drawing edge port.dir = vertex := by
    have hd := (native_dart_port_iff input.graph hg.1 drawing vertex edge port.dir).mpr ⟨weight, horig⟩
    rw [native_dart_vertex] at hd
    apply Fin.ext
    simpa only [endVertex, apply_ite] using hd
  refine ⟨edge, rfl, hv, ?_⟩
  simp only [endToken, hv]
  exact corePortToken_eq width input hg vertex hp

/-- An actual rotation retains its precise original edge, endpoint tag, and native vertex. -/
theorem coreRotation_end (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) {port : NCL.Port ℕ} {weight : ℕ}
    (hp : (.rotation vertex.val true, ⟨port, weight⟩) ∈ (coreBlock width input vertex.val).core.ports) :
    ∃ edge : Fin input.graph.edgeCount, edge.val = port.edge ∧
      endVertex input drawing edge port.dir = vertex ∧
      endToken width input drawing edge port.dir = .rotation vertex.val true :=
  corePort_end width input hg drawing vertex hp

/-- An actual native endpoint axis retains precisely its original orientation bit. -/
theorem ConfigurationInput.endToken_bit (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (drawing : NCL.GridDrawing.Closed x.input.graph.graph)
    (edge : Fin x.input.graph.edgeCount) (side : Bool) :
    x.tokenBit width (endToken width x.input drawing edge side) =
      (x.bits.getD edge.val false ^^ side) := by
  obtain ⟨weight, hp⟩ := endVertex_port x.input hg drawing edge side
  exact x.corePort_bit width hg (endVertex x.input drawing edge side).isLt
    (corePortToken_spec width x.input hg _ hp)

/-- Traverse a native endpoint's actual rotation from core to original route, or back. -/
@[expose] def endExtension (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) : List Token :=
  if endToken width input drawing edge side = .tip edge.val side then []
  else if side then [.rotation (endVertex input drawing edge side).val false,
    .rotation (endVertex input drawing edge side).val true]
  else [.rotation (endVertex input drawing edge side).val true,
    .rotation (endVertex input drawing edge side).val false]

/-- Traversing a genuine native rotation retains its two literal inside/outside axes. -/
theorem endExtension_of_rotation (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) (vertex : Fin input.graph.vertices.length)
    (hv : endVertex input drawing edge side = vertex)
    (ht : endToken width input drawing edge side = .rotation vertex.val true) :
    endExtension width input drawing edge side =
      if side then [.rotation vertex.val false, .rotation vertex.val true]
      else [.rotation vertex.val true, .rotation vertex.val false] := by
  simp only [endExtension, ht, reduceCtorEq, ite_false, hv]

/-- The complete actual axes, from the original false core to the original true core. -/
@[expose] def axisVisits (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) : List Token :=
  endExtension width input drawing edge false ++ edgeVisits width input.drawing edge.val ++
    endExtension width input drawing edge true

/-- Each actual endpoint rotation contributes either zero or two consecutive axis segments. -/
theorem endExtension_length (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) :
    (endExtension width input drawing edge side).length = 0 ∨
      (endExtension width input drawing edge side).length = 2 := by
  unfold endExtension
  split_ifs <;> simp

/-- The actual chain has a positive even number of segments. -/
theorem axisVisits_length (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) :
    2 ≤ (axisVisits width input drawing edge).length ∧
      (axisVisits width input drawing edge).length % 2 = 0 := by
  have ha := endExtension_length width input drawing edge false
  have hb := endExtension_length width input drawing edge true
  simp only [axisVisits, List.length_append, edgeVisits_length]
  rcases ha with ha | ha <;> rcases hb with hb | hb <;> omega

/-- The first actual axis is the original false native core incidence. -/
theorem axisVisits_head (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    (axisVisits width input drawing edge).head? = some (endToken width input drawing edge false) := by
  by_cases h : endToken width input drawing edge false = .tip edge.val false
  · simp [axisVisits, endExtension, h, edgeVisits]
  · have hr := (endToken_role width input hg drawing edge false).resolve_left h
    simp [axisVisits, endExtension, hr]

/-- The last actual axis is the original true native core incidence. -/
theorem axisVisits_last (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    (axisVisits width input drawing edge).getLast? = some (endToken width input drawing edge true) := by
  by_cases h : endToken width input drawing edge true = .tip edge.val true
  · have he : (edgeVisits width input.drawing edge.val).getLast? = some (.tip edge.val true) := by
      change (_ ++ [Token.tip edge.val true]).getLast? = _
      exact List.getLast?_append_of_ne_nil _ (by simp)
    simp [axisVisits, endExtension, h, he]
  · have hr := (endToken_role width input hg drawing edge true).resolve_left h
    simp [axisVisits, endExtension, hr]

private theorem endExtension_mem (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) {token : Token}
    (ht : token ∈ endExtension width input drawing edge side) :
    ∃ b, token = .rotation (endVertex input drawing edge side).val b := by
  unfold endExtension at ht
  split_ifs at ht <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  all_goals rcases ht with rfl | rfl <;> exact ⟨_, rfl⟩

private theorem endExtension_nodup (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) :
    (endExtension width input drawing edge side).Nodup := by
  unfold endExtension
  split_ifs <;> simp

private theorem endExtension_edgeVisits_disjoint (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) (other : ℕ) :
    (endExtension width input drawing edge side).Disjoint (edgeVisits width input.drawing other) := by
  apply List.disjoint_left.mpr
  intro token ht hv
  obtain ⟨b, rfl⟩ := endExtension_mem width input drawing edge side ht
  rcases (edgeVisits_mem width input.drawing other _).mp hv with h | h | ⟨c, _, _, h | h⟩
  all_goals cases h

private theorem endExtensions_disjoint (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    (endExtension width input drawing edge false).Disjoint
      (endExtension width input drawing edge true) := by
  apply List.disjoint_left.mpr
  intro token hl hr
  obtain ⟨s, hs⟩ := endExtension_mem width input drawing edge false hl
  obtain ⟨t, ht⟩ := endExtension_mem width input drawing edge true hr
  have hp := (Token.rotation.inj (hs.symm.trans ht)).1
  exact drawing.source_ne_target edge (Fin.ext hp)

/-- Every actual axis in one complete original-edge chain occurs exactly once. -/
theorem axisVisits_nodup (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    (axisVisits width input drawing edge).Nodup := by
  apply ((endExtension_nodup width input drawing edge false).append
    (edgeVisits_nodup width input.drawing edge.val)
    (endExtension_edgeVisits_disjoint width input drawing edge false edge.val)).append
    (endExtension_nodup width input drawing edge true)
  exact List.disjoint_append_left.mpr ⟨endExtensions_disjoint width input drawing edge,
    (endExtension_edgeVisits_disjoint width input drawing edge true edge.val).symm⟩

private theorem extension_endToken (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (edge : Fin input.graph.edgeCount) (side : Bool) {token : Token}
    (ht : token ∈ endExtension width input drawing edge side) :
    endToken width input drawing edge side =
      .rotation (endVertex input drawing edge side).val true := by
  by_cases h : endToken width input drawing edge side = .tip edge.val side
  · simp only [endExtension, h, ite_true, List.not_mem_nil] at ht
  · exact (endToken_role width input hg drawing edge side).resolve_left h

private theorem different_extensions_disjoint (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    {left right : Fin input.graph.edgeCount} (hne : left ≠ right) (s t : Bool) :
    (endExtension width input drawing left s).Disjoint
      (endExtension width input drawing right t) := by
  apply List.disjoint_left.mpr
  intro token hl hr
  obtain ⟨a, ha⟩ := endExtension_mem width input drawing left s hl
  obtain ⟨b, hb⟩ := endExtension_mem width input drawing right t hr
  have hv := (Token.rotation.inj (ha.symm.trans hb)).1
  have he : endToken width input drawing left s = endToken width input drawing right t := by
    rw [extension_endToken width input hg drawing left s hl,
      extension_endToken width input hg drawing right t hr, hv]
  exact hne (endToken_injective width input hg drawing left right s t he).1

private theorem different_edgeVisits_disjoint (width : ℕ) (d : Graph.OrthogonalDrawing)
    {left right : ℕ} (hne : left ≠ right) :
    (edgeVisits width d left).Disjoint (edgeVisits width d right) := by
  apply List.disjoint_left.mpr
  intro token hl hr
  rcases edgeVisits_shape width d left hl with ⟨s, hs⟩ | ⟨i, v, s, hs⟩ <;>
    rcases edgeVisits_shape width d right hr with ⟨t, ht⟩ | ⟨j, w, t, ht⟩
  · exact hne (Token.tip.inj (hs.symm.trans ht)).1
  · cases hs.symm.trans ht
  · cases hs.symm.trans ht
  · exact hne (Token.mark.inj (hs.symm.trans ht)).1

/-- Different original edges use disjoint actual axis chains, including their native rotations.
-/
theorem axisVisits_disjoint (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    {left right : Fin input.graph.edgeCount} (hne : left ≠ right) :
    (axisVisits width input drawing left).Disjoint (axisVisits width input drawing right) := by
  simp only [axisVisits, List.disjoint_append_left, List.disjoint_append_right]
  repeat' apply And.intro
  all_goals first
    | exact different_extensions_disjoint width input hg drawing hne _ _
    | exact endExtension_edgeVisits_disjoint width input drawing left _ right.val
    | exact (endExtension_edgeVisits_disjoint width input drawing right _ left.val).symm
    | exact different_edgeVisits_disjoint width input.drawing (fun h => hne (Fin.ext h))

end PushPuzzle.PushS.Comb

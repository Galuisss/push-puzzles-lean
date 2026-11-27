/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionCursor
import all PushS.CombSubdivisionCores
import all PushS.CombSubdivisionSimulation
import all PushS.CombNormalizedInputs
import all PushS.PortConstraintGraph

/-! The actual normalized source emission lies in the same original subdivision component. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL NCL.ConstraintGraph NCL.ConstraintGraph.Subdivision

private theorem normalized_core_input (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (vertex : Fin x.input.graph.vertices.length) {token : Token} {port : Port ℕ} {weight : ℕ}
    (hp : (token, ⟨port, weight⟩) ∈ (coreBlock width x.input vertex.val).core.ports)
    (hfalse : (x.normalizedAxes width).getD ((cut width x.input).rank token) false = false) :
    x.portBit port = false := by
  obtain ⟨a, b, c, hports, hgate⟩ := vertexBlock_core_group width x.input vertex.val
  have htoken : token ∈ [a, b, c] := by
    rw [← hports]
    exact List.mem_map.mpr ⟨_, hp, rfl⟩
  have ht : token ∈ (vertexBlock width x.input vertex.val).order :=
    lower_token width x.input vertex.val hgate htoken
  rw [x.normalizedAxes_rank width hg hcount vertex.isLt ht,
    x.normalized_corePort_bit width hg vertex.isLt hp] at hfalse
  split_ifs at hfalse
  exact hfalse

private theorem actual_direction_eq (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    (drawing : GridDrawing.Closed x.input.graph.graph) :
    (compile width x.input).graphData.config (x.normalizedAxes width) ∘
        subdivisionNativeEquiv width x.input hg hcount hedges drawing =
      (fun token => (x.normalizedAxes width).getD ((cut width x.input).rank token) false) ∘
        segmentToken width x.input drawing := by
  funext segment
  change (x.normalizedAxes width).getD _ false = _
  rw [subdivisionNativeEquiv_val, subdivisionAxisEquiv_val]
  rfl

private theorem normalized_subdivision_input (width : ℕ) (x : ConfigurationInput) (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    (drawing : GridDrawing.Closed x.input.graph.graph)
    (vertex : Fin x.input.graph.vertices.length) (p : WeightedPort (Fin x.input.graph.edgeCount))
    (hp : p ∈ (x.input.graph.graph vertex).ports)
    (hin : (⟨if p.1.dir then last (axisJointCount width x.input drawing) p.1.edge
        else first (axisJointCount width x.input drawing) p.1.edge, p.1.dir⟩ :
      Port (Segment (axisJointCount width x.input drawing))).In
        (axisParity width x.input drawing +
          (compile width x.input).graphData.config (x.normalizedAxes width) ∘
            subdivisionNativeEquiv width x.input hg hcount hedges drawing)) :
    p.1.In (x.input.graph.config x.bits) := by
  have ha := (Port.in_reorient _ _ _).mpr hin
  rw [actual_direction_eq width x hg hcount hedges drawing] at ha
  have hfalse := (subdivisionPort_in width x.input hg drawing p.1
    (fun token => (x.normalizedAxes width).getD ((cut width x.input).rank token) false)).mp ha
  rw [endToken_at_port width x.input drawing vertex p.1 hp] at hfalse
  have hraw := (native_weighted_port_iff x.input.graph hg.1 vertex p.1.edge p.1.dir p.2).mp hp
  have hbit := normalized_core_input width x hg hcount vertex
    (corePortToken_spec width x.input hg vertex hraw) hfalse
  exact (x.portBit_eq_false _).mp hbit

/-- The actual raw and normalized emissions are connected in the same native contour graph. -/
theorem ConfigurationInput.normalizedAxes_nativeReachable (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph) (hs : x.input.graph.graph.Legal (x.input.graph.config x.bits))
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    (drawing : GridDrawing.Closed x.input.graph.graph) :
    (compile width x.input).graphData.graph.Reachable
      ((compile width x.input).graphData.config (x.axes width))
      ((compile width x.input).graphData.config (x.normalizedAxes width)) := by
  let n := axisJointCount width x.input drawing
  let original := graph x.input.graph.graph n (fun _ => 1)
  let mask := axisParity width x.input drawing
  let actual := (compile width x.input).graphData.config (x.normalizedAxes width) ∘
    subdivisionNativeEquiv width x.input hg hcount hedges drawing
  have ht := (axisGraph_legal_iff_inputLegal width x.input hg hcount hedges drawing _
    (length_normalizedAxes width x)).mpr
      (x.normalizedAxes_orderedInputs width hg hs hcount hedges).toInputLegal
  have hlegal : original.Legal (mask + actual) := (original.legal_reorient mask actual).mp ht
  have hsub := subdivision_reachable_of_core_inputs x.input.graph.graph n (fun _ => 1)
    (fun _ => by omega) hg.loopFree _ hs _ hlegal
      (normalized_subdivision_input width x hg hcount hedges drawing)
  have hr := (original.reorientSimulation mask).toSimulation.reachable_enc hsub
  change (axisGraph width x.input drawing).Reachable (mask + enc n (x.input.graph.config x.bits))
    (mask + (mask + actual)) at hr
  rw [Cslib.BitString.add_cancel_left] at hr
  have hactual := (renamingSimulation width x.input hg hcount hedges drawing).toSimulation.reachable_enc hr
  change (compile width x.input).graphData.graph.Reachable
    ((contourSimulation width x.input hg hcount hedges drawing).enc (x.input.graph.config x.bits))
    (actual ∘ (subdivisionNativeEquiv width x.input hg hcount hedges drawing).symm) at hactual
  have he : actual ∘ (subdivisionNativeEquiv width x.input hg hcount hedges drawing).symm =
      (compile width x.input).graphData.config (x.normalizedAxes width) := by
    funext axis
    exact congrArg ((compile width x.input).graphData.config (x.normalizedAxes width))
      ((subdivisionNativeEquiv width x.input hg hcount hedges drawing).apply_symm_apply axis)
  rwa [x.contourSimulation_enc width hg hcount hedges drawing, he] at hactual

/-- Normalizing the original legal endpoint configurations preserves and reflects actual axis reachability.
-/
theorem normalizedAxes_reachable_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : GridDrawing.Closed input.graph.graph) (initial target : List Bool)
    (hi : input.graph.graph.Legal (input.graph.config initial))
    (ht : input.graph.graph.Legal (input.graph.config target)) :
    input.graph.graph.Reachable (input.graph.config initial) (input.graph.config target) ↔
      Relation.ReflTransGen (compile width input).AxisStep
        (ConfigurationInput.normalizedAxes width ⟨input, initial⟩)
        (ConfigurationInput.normalizedAxes width ⟨input, target⟩) := by
  let simulation := contourSimulation width input hg hcount hedges drawing
  have hi' := ConfigurationInput.normalizedAxes_nativeReachable width ⟨input, initial⟩ hg hi hcount hedges drawing
  have ht' := ConfigurationInput.normalizedAxes_nativeReachable width ⟨input, target⟩ hg ht hcount hedges drawing
  rw [← (compile width input).graphData_reachable_iff (compile_graphData_bounded width input hg hcount hedges)
    _ _ (length_normalizedAxes width ⟨input, initial⟩) (length_normalizedAxes width ⟨input, target⟩)]
  have hraw := simulation.toSimulation.reachable_enc_iff (a := input.graph.config initial) (a' := input.graph.config target)
  rw [ConfigurationInput.contourSimulation_enc width ⟨input, initial⟩ hg hcount hedges drawing,
    ConfigurationInput.contourSimulation_enc width ⟨input, target⟩ hg hcount hedges drawing] at hraw
  exact hraw.symm.trans ⟨fun h => hi'.symm.trans (h.trans ht'), fun h => hi'.trans (h.trans ht'.symm)⟩

end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSubdivisionLegal
import all PushS.PortConstraintGraph

/-! The same original native graph is simulated by the actual emitted port layout. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL.ConstraintGraph

private theorem native_legal_renaming (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (s : Subdivision.Segment (axisJointCount width input drawing) → Bool) :
    (compile width input).graphData.graph.Legal
      (s ∘ (subdivisionNativeEquiv width input hg hcount hedges drawing).symm) ↔
      (axisGraph width input drawing).Legal s := by
  let native := (compile width input).graphData
  let equiv := subdivisionNativeEquiv width input hg hcount hedges drawing
  let direction := s ∘ equiv.symm
  let axes := List.ofFn direction
  have hlen : axes.length = (compile width input).portCount := by
    rw [List.length_ofFn, PortLayout.graphData_edgeCount]
  have hcfg : native.config axes = direction := native.config_ofFn direction
  have hsource : native.config axes ∘ equiv = s := by
    rw [hcfg]
    funext segment
    exact congrArg s (equiv.symm_apply_apply segment)
  have hactual := axisGraph_legal_iff_inputLegal width input hg hcount hedges drawing axes hlen
  rw [hsource] at hactual
  rw [hactual]
  have hnative := (compile width input).graphData_legal_iff
    (compile_graphData_bounded width input hg hcount hedges) axes hlen
  rw [hcfg] at hnative
  exact hnative

private noncomputable def renamingSimulation (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    Simulation (axisGraph width input drawing) (compile width input).graphData.graph :=
  .ofLegalEquiv _ _ (subdivisionNativeEquiv width input hg hcount hedges drawing)
    (native_legal_renaming width input hg hcount hedges drawing)

/-- The same actual contour is the original graph's standard native subdivision and renaming.
-/
noncomputable def contourSimulation (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    Simulation input.graph.graph (compile width input).graphData.graph :=
  ((Subdivision.simulation input.graph.graph (axisJointCount width input drawing) (fun _ => 1)
    (fun _ => by omega) hg.loopFree).trans
    ((Subdivision.graph input.graph.graph (axisJointCount width input drawing) (fun _ => 1)).reorientSimulation
      (axisParity width input drawing))).trans (renamingSimulation width input hg hcount hedges drawing)

/-- Its standard simulation encoding is exactly the same original actual contour-bit emitter. -/
theorem ConfigurationInput.contourSimulation_enc (width : ℕ) (x : ConfigurationInput)
    (hg : NCL.SourceValid x.input.graph)
    (hcount : x.input.drawing.1.length = x.input.graph.vertices.length)
    (hedges : x.input.drawing.2.length = x.input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed x.input.graph.graph) :
    (contourSimulation width x.input hg hcount hedges drawing).enc (x.input.graph.config x.bits) =
      (compile width x.input).graphData.config (x.axes width) := by
  funext axis
  let equiv := subdivisionNativeEquiv width x.input hg hcount hedges drawing
  let segment := equiv.symm axis
  change (axisParity width x.input drawing segment ^^
    Subdivision.enc (axisJointCount width x.input drawing) (x.input.graph.config x.bits) segment) = _
  have hread := x.axes_subdivisionAxisEquiv width hg hcount hedges drawing segment
  have haxis := congrArg (fun i : Fin (compile width x.input).graphData.edgeCount => i.val)
    (equiv.apply_symm_apply axis)
  change (subdivisionNativeEquiv width x.input hg hcount hedges drawing segment).val = axis.val at haxis
  rw [subdivisionNativeEquiv_val] at haxis
  rw [haxis] at hread
  exact hread.symm

/-- Original native reachability is exactly reachability of the actual emitted axis arrays. -/
theorem rawAxes_reachable_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length)
    (hedges : input.drawing.2.length = input.graph.edgeCount)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (initial target : List Bool) :
    input.graph.graph.Reachable (input.graph.config initial) (input.graph.config target) ↔
      Relation.ReflTransGen (compile width input).AxisStep
        (ConfigurationInput.axes width ⟨input, initial⟩) (ConfigurationInput.axes width ⟨input, target⟩) := by
  rw [← (compile width input).graphData_reachable_iff
    (compile_graphData_bounded width input hg hcount hedges) _ _
      (length_axes width ⟨input, initial⟩) (length_axes width ⟨input, target⟩),
    ← ConfigurationInput.contourSimulation_enc width ⟨input, initial⟩ hg hcount hedges drawing,
    ← ConfigurationInput.contourSimulation_enc width ⟨input, target⟩ hg hcount hedges drawing]
  exact (contourSimulation width input hg hcount hedges drawing).toSimulation.reachable_enc_iff.symm

end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombAxisDirections
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.Reorient
import all PushS.CombCore

/-! Standard native subdivision retains exactly the actual weighted constraints at every core. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open NCL.ConstraintGraph

/-- The original standard native subdivision, in the actual contour axes' reference directions.
-/
@[expose] def axisGraph (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) :
    NCL.ConstraintGraph
      (Fin input.graph.vertices.length ⊕ Subdivision.Joint (axisJointCount width input drawing))
      (Subdivision.Segment (axisJointCount width input drawing)) :=
  (Subdivision.graph input.graph.graph (axisJointCount width input drawing) (fun _ => 1)).reorient
    (axisParity width input drawing)

/-- The first standard segment is the same actual original false core token. -/
theorem segmentToken_first (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    segmentToken width input drawing (Subdivision.first (axisJointCount width input drawing) edge) =
      endToken width input drawing edge false := by
  have hh : (axisVisits width input drawing edge).getD 0 (.tip 0 false) =
      endToken width input drawing edge false := by
    rw [List.getD_eq_getElem?_getD, ← List.head?_eq_getElem?, axisVisits_head width input hg drawing edge]
    rfl
  change (axisVisits width input drawing edge).get ⟨0, _⟩ = _
  exact (List.getD_eq_get _ _ ⟨0, by have hp := (axisVisits_length width input drawing edge).1; omega⟩).symm.trans hh

/-- The last standard segment is the same actual original true core token. -/
theorem segmentToken_last (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph) (edge : Fin input.graph.edgeCount) :
    segmentToken width input drawing (Subdivision.last (axisJointCount width input drawing) edge) =
      endToken width input drawing edge true := by
  have hh : (axisVisits width input drawing edge).getD (axisJointCount width input drawing edge) (.tip 0 false) =
      endToken width input drawing edge true := by
    rw [axisJointCount, List.getD_eq_getElem?_getD, ← List.getLast?_eq_getElem?,
      axisVisits_last width input hg drawing edge]
    rfl
  change (axisVisits width input drawing edge).get ⟨axisJointCount width input drawing edge, _⟩ = _
  exact (List.getD_eq_get _ _ ⟨axisJointCount width input drawing edge,
    by rw [← axisJointCount_add_one]; omega⟩).symm.trans hh

/-- Every original native port reads its actual same-vertex weighted metadata token. -/
theorem endToken_at_port (width : ℕ) (input : Input)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) (port : NCL.Port (Fin input.graph.edgeCount))
    {weight : ℕ} (hp : (⟨port, weight⟩ : NCL.WeightedPort (Fin input.graph.edgeCount)) ∈ (input.graph.graph vertex).ports) :
    endToken width input drawing port.edge port.dir =
      (coreBlock width input vertex.val).core.portToken (port.map Fin.val) := by
  have hv : endVertex input drawing port.edge port.dir = vertex := by
    cases port with
    | mk edge side =>
      cases side with
      | false => exact drawing.source_eq vertex edge ⟨weight, hp⟩
      | true => exact drawing.target_eq vertex edge ⟨weight, hp⟩
  simp only [endToken, hv, NCL.Port.map]

private theorem subdivisionPort_in (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (port : NCL.Port (Fin input.graph.edgeCount)) (direction : Token → Bool) :
    ((⟨if port.dir then Subdivision.last (axisJointCount width input drawing) port.edge
        else Subdivision.first (axisJointCount width input drawing) port.edge, port.dir⟩ :
      NCL.Port (Subdivision.Segment (axisJointCount width input drawing))).reorient
        (axisParity width input drawing)).In (direction ∘ segmentToken width input drawing) ↔
      direction (endToken width input drawing port.edge port.dir) = false := by
  rcases port with ⟨edge, side⟩
  cases side <;> simp only [ite_true, Bool.false_eq_true, ite_false, NCL.Port.In,
    NCL.Port.reorient, Function.comp_apply]
  all_goals simp only [axisParity_first, axisParity_last, Bool.false_xor, Bool.true_xor,
    Bool.not_true, segmentToken_first width input hg drawing, segmentToken_last width input hg drawing]

private theorem subdivision_core_inflow (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) (direction : Token → Bool) :
    (axisGraph width input drawing (.inl vertex)).inflow (direction ∘ segmentToken width input drawing) =
      ((coreBlock width input vertex.val).core.ports.map
        (fun (token, ⟨_, weight⟩) => if direction token = false then weight else 0)).sum := by
  let term := fun p : NCL.WeightedPort ℕ =>
    if direction ((coreBlock width input vertex.val).core.portToken p.1) = false then p.2 else 0
  have hfinite : (axisGraph width input drawing (.inl vertex)).inflow
      (direction ∘ segmentToken width input drawing) =
      ((input.graph.graph vertex).ports.map (fun p => term (NCL.WeightedPort.map Fin.val p))).sum := by
    simp only [axisGraph, reorient, Subdivision.graph, NCL.Vertex.reorient, NCL.WeightedPort.reorient, NCL.Vertex.inflow,
      List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro p hp
    have hin := subdivisionPort_in width input hg drawing p.1 direction
    simp only [Function.comp_def] at hin
    simp only [hin, endToken_at_port width input drawing vertex p.1 hp, term, NCL.WeightedPort.map]
  rw [hfinite]
  have hp := congrArg NCL.Vertex.ports (congrFun (input.graph.graph_map_val hg.1) vertex)
  change (input.graph.graph vertex).ports.map (NCL.WeightedPort.map Fin.val) =
    (input.graph.vertices.get vertex).ports at hp
  have hp' := congrArg (fun ports => (ports.map term).sum) hp
  simp only [List.map_map, Function.comp_def] at hp'
  rw [hp']
  have hc := coreBlock_ports_perm width input hg vertex.isLt
  rw [List.getD_eq_get _ _ vertex] at hc
  rw [← (hc.map term).sum_nat, List.map_map]
  congr 1
  apply List.map_congr_left
  intro tp ht
  simp only [Function.comp_apply, term, corePortToken_eq width input hg vertex ht]

/-- An arbitrary actual axis orientation satisfies an original core exactly at its actual weighted threshold.
-/
theorem axisGraph_core_sat_iff (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (drawing : NCL.GridDrawing.Closed input.graph.graph)
    (vertex : Fin input.graph.vertices.length) (direction : Token → Bool) :
    (axisGraph width input drawing (.inl vertex)).Sat (direction ∘ segmentToken width input drawing) ↔
      2 ≤ ((coreBlock width input vertex.val).core.ports.map
        (fun (token, ⟨_, weight⟩) => if direction token = false then weight else 0)).sum := by
  change (axisGraph width input drawing (.inl vertex)).minInflow ≤ _ ↔ _
  rw [subdivision_core_inflow width input hg drawing vertex direction]
  have hm := (hg.isAndOr vertex).shape.2
  exact (congrArg (fun bound => bound ≤ _) hm).to_iff

end PushPuzzle.PushS.Comb

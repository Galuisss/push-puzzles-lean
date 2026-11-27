/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Timeline
public import PushS.Source.Strip.Sweep.Cell.Resources
public import PushS.Source.Strip.Sweep.StageBlocks
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.RowBandwidth
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileBandwidth

/-!
# Actual scan stages in the actual emitted vertex order

The vertex stages are actual consecutive implementation blocks in compilation order. Each
block contains a fixed number of vertices, bounded by the actual local alphabet budget.
The actual compilation order therefore bounds the index distance of every actual edge.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.stages`: actual scan-stage metadata in actual vertex compilation order.
* `PushPuzzle.NCL.Strip.Sweep.Context.stageCertificate`: the actual vertex order, with its derived edge span.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.stage_fiber_le`: actual stage fibers have constant size.
* `PushPuzzle.NCL.Strip.Sweep.Context.stage_monotone`: actual compilation order is monotone in actual stage.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

private theorem retype_vertexCount {a b a' b' : List Color} (D : Diagram Cell a b)
    (ha : a = a') (hb : b = b') :
    (vertexList Prim.interp ((PushPuzzle.NCL.Strip.Sweep.Cell.retype D ha hb).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length =
      (vertexList Prim.interp (D.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length := by
  cases ha
  cases hb
  rfl

/-- Every actual scan step emits at most the fixed local alphabet's actual vertex budget. -/
private theorem stepVertexCount_le (t : ℤ) :
    (vertexList Prim.interp ((C.stepDiagram t).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length ≤
      PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := by
  apply C.frame_cases t (fun f =>
    (vertexList Prim.interp (f.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length ≤ PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget)
  · intro hc
    dsimp only [emptyFrame, emptyDiagram]
    have hr := retype_vertexCount (Diagram.id (Γ := Cell) (C.frontierColors t)) rfl
      (congrArg (List.map (fun a : Arc C.environment => C.color a.edge)) (C.empty_frontier t hc))
    exact hr.le.trans (show 0 ≤ PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget from Nat.zero_le _)
  · intro site hc
    simp only [cellFrame, cellDiagram, retype_vertexCount, Diagram.pad, Diagram.subst, vertexList,
      List.length_append, List.length_map, List.length_nil, Nat.zero_add, Nat.add_zero]
    exact PushPuzzle.NCL.Strip.Sweep.Cell.vertexCount_le _

/-- The actual number of standard vertices emitted at one actual scan stage. -/
@[expose] def stepVertexCount (i : ℕ) : ℕ :=
  (vertexList Prim.interp ((C.stepDiagram i).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length

/-- Actual chronological scan-stage blocks, in the actual vertex compilation order. -/
@[expose] def stages : List ℕ :=
  stageBlocks C.stepVertexCount (scanLength C.environment (List.finRange C.source.edgeCount))

/-- The explicit stage metadata is the actual expanded graph's actual vertex-label stream. -/
private theorem stages_eq_vertexLabels :
    C.stages = vertexLabels Prim.interp C.expandedDiagram C.timeline.stage :=
  C.timeline_vertexLabels.symm

/-- Every actual scan-stage fiber contains at most the fixed local vertex budget. -/
theorem stage_fiber_le (r : ℕ) :
    Nat.card {v : C.expandedDiagram.Vtx Prim.interp // C.timeline.stage v = r} ≤
      PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := by
  rw [← count_vertexLabels Prim.interp C.expandedDiagram C.timeline.stage r,
    ← C.stages_eq_vertexLabels, stages, count_stageBlocks]
  split_ifs
  · exact C.stepVertexCount_le r
  · exact Nat.zero_le _

/-- The actual finite vertex compilation order is monotone in actual source scan stage. -/
theorem stage_monotone :
    Monotone (fun i => C.timeline.stage ((vertexEquiv Prim.interp C.expandedDiagram).symm i)) := by
  have hs : (vertexLabels Prim.interp C.expandedDiagram C.timeline.stage).Pairwise (· ≤ ·) := by
    rw [← C.stages_eq_vertexLabels]
    exact stageBlocks_sorted _ _
  rw [vertexLabels_eq_ofFn] at hs
  have hr := List.pairwise_ofFn.mp hs
  intro i j hij
  rcases eq_or_lt_of_le hij with rfl | hlt
  · exact le_rfl
  · exact hr hlt

/-- The actual standard vertex compilation order has the derived constant edge span. -/
@[expose] noncomputable def stageCertificate :
    ConstraintGraph.BandwidthCertificate (C.expandedDiagram.graph Prim.interp)
      ((height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1) :=
  ConstraintGraph.BandwidthCertificate.ofRowOrder _
    (vertexEquiv Prim.interp C.expandedDiagram) C.timeline.stage C.stage_fiber_le C.stage_monotone
    (fun u v p hp q hq he => by
      have h := C.expanded_stage_edge_bounds u v hp hq he
      simp only [Nat.dist]
      omega)

private theorem compiled_vertex_index_bounds :
    let G := (C.expandedDiagram.toWord Prim.interp 0).compile.graph
    ∀ u v, ∀ p ∈ (G u).ports, ∀ q ∈ (G v).ports, p.1.edge = q.1.edge →
      Nat.dist u.val v.val ≤ (height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1 := by
  intro G u v p hp q hq he
  let B := compileBandwidthCertificate Prim.interp C.expandedDiagram C.stageCertificate
  have h := B.span u v p hp q hq he
  change Nat.dist
    ((vertexEquiv Prim.interp C.expandedDiagram)
      ((compileVertexEquiv Prim.interp C.expandedDiagram).symm u)).val
    ((vertexEquiv Prim.interp C.expandedDiagram)
      ((compileVertexEquiv Prim.interp C.expandedDiagram).symm v)).val ≤ _ at h
  simpa only [compileVertexEquiv_symm_val] using h

/-- The same native output's actual vertex-list indices have the derived constant edge span. -/
theorem program_vertex_index_bounds :
    ∀ u v, ∀ p ∈ (C.program.compile.graph u).ports, ∀ q ∈ (C.program.compile.graph v).ports,
      p.1.edge = q.1.edge →
        Nat.dist u.val v.val ≤ (height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1 := by
  exact C.expanded_word ▸ C.compiled_vertex_index_bounds

end PushPuzzle.NCL.Strip.Sweep.Context

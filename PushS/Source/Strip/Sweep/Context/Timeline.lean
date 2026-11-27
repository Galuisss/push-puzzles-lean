/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Labels
public import PushS.Source.Strip.Sweep.Context.Expansion
public import PushS.Source.Strip.Sweep.Timeline
public import PushS.Source.Strip.Sweep.Lifetime

/-!
# Actual source scan stages of the expanded strip graph

Each actual unit arc is owned by its actual birth scan position. Local implementations retain
those boundary owners and assign the current stage to new internal edges and vertices. The
resulting timeline is constructed through the same actual typed scan diagram.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.stepTimeline`: the actual timeline of one actual local expansion.
* `PushPuzzle.NCL.Strip.Sweep.Context.timeline`: the actual timeline of the complete expanded diagram.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.expanded_stage_edge_bounds`: endpoints of the same actual expanded edge
  belong to scan stages at most one fixed scan radix apart.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- Actual unit-arc birth owners on the actual frontier at one scan cut. -/
@[expose] def birthFrontier (t : ℤ) : List ℤ := (C.frontier t).map (PushPuzzle.NCL.Strip.Sweep.Arc.birth C.environment)

private theorem step_birth_bounds (t : ℤ) (e : (C.stepDiagram t).Edge) :
    ((C.stepLabeling t).label e).birth C.environment ≤ t ∧
      t ≤ ((C.stepLabeling t).label e).birth C.environment + (height K + 1 : ℕ) := by
  have hm := (PushPuzzle.NCL.Diagram.Labeling.mem_top_or_created (C.stepLabeling t)) e
  simp only [C.stepLabeling_created] at hm
  rcases List.mem_append.mp hm with hi | ho
  · have ha := ((mem_frontier C.environment _ t _).mp hi).2
    have hs := ((C.stepLabeling t).label e).level_span_le C.environment
    dsimp only [PushPuzzle.NCL.Strip.Sweep.Arc.birth] at hs ⊢
    dsimp only [PushPuzzle.NCL.Strip.Sweep.Arc.Active] at ha
    omega
  · exact local_birth_bounds C.environment _ t (List.mem_append_right _ ho)

/-- One actual local implementation retains actual arc owners and uses the current stage inside.
-/
@[expose] noncomputable def stepTimeline (n : ℕ) :
    TimelineLabeling ((C.stepDiagram n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) (height K + 1)
      (C.birthFrontier n) (C.birthFrontier ((n : ℤ) + 1)) :=
  PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.ofOpenSim ((PushPuzzle.NCL.Diagram.Labeling.map (C.stepLabeling n)) (PushPuzzle.NCL.Strip.Sweep.Arc.birth C.environment))
    (openSimSubst PushPuzzle.NCL.Strip.Sweep.Cell.expandOpenSim (C.stepDiagram n)) n (by exact C.step_birth_bounds n)

/-- Stack the actual expanded local timelines through the first `n` original grid sites. -/
@[expose] noncomputable def prefixTimeline : (n : ℕ) →
    TimelineLabeling ((C.diagramPrefix n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) (height K + 1)
      (C.birthFrontier 0) (C.birthFrontier n)
  | 0 =>
    { labels := Labeling.id _ _ (by
        simp only [birthFrontier, frontierColors, frontier, List.length_map])
      stage := Empty.elim
      localPort := fun v => v.elim }
  | n + 1 =>
    let h : (n : ℤ) + 1 = (n + 1 : ℕ) := by omega
    let L := PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.retypeRaw
      (D := (C.diagramPrefix n).comp (C.stepDiagram n))
      ((prefixTimeline n).comp (C.stepTimeline n)) rfl (congrArg C.frontierColors h)
    L.castLabels rfl (congrArg C.birthFrontier h)

/-- The actual complete expanded graph, with its actual edge owners and vertex scan stages. -/
@[expose] noncomputable def timeline :
    TimelineLabeling C.expandedDiagram (height K + 1) [] [] :=
  let L := PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.retypeRaw (D := C.diagramPrefix
      (scanLength C.environment (List.finRange C.source.edgeCount))) (C.prefixTimeline _)
    (by simp only [frontierColors, frontier_zero, List.map_nil])
    (by simp only [frontierColors, frontier_scanLength, List.map_nil])
  L.castLabels (by simp only [birthFrontier, frontier, frontier_zero, List.map_nil])
    (by simp only [birthFrontier, frontier, frontier_scanLength, List.map_nil])

/-- Every actual local expanded vertex receives precisely its actual scan position. -/
private theorem stepTimeline_vertexLabels (n : ℕ) :
    vertexLabels Prim.interp ((C.stepDiagram n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) (C.stepTimeline n).stage =
      List.replicate (vertexList Prim.interp ((C.stepDiagram n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length n :=
  vertexLabels_const Prim.interp _ n

/-- The actual expanded prefix lists its vertex stages as the actual consecutive local blocks.
-/
private theorem prefixTimeline_vertexLabels (n : ℕ) :
    vertexLabels Prim.interp ((C.diagramPrefix n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand) (C.prefixTimeline n).stage =
      (List.range n).flatMap (fun (i : ℕ) => List.replicate
        (vertexList Prim.interp ((C.stepDiagram i).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length i) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [diagramPrefix, prefixTimeline, PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.vertexLabels_castLabels,
      List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    have hr := PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.vertexLabels_retypeRaw
      (D := (C.diagramPrefix n).comp (C.stepDiagram n))
      ((C.prefixTimeline n).comp (C.stepTimeline n)) rfl
      (congrArg C.frontierColors (show (n : ℤ) + 1 = (n + 1 : ℕ) by omega))
    apply hr.trans
    change vertexLabels Prim.interp
      (((C.diagramPrefix n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).comp ((C.stepDiagram n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand))
      ((C.prefixTimeline n).comp (C.stepTimeline n)).stage = _
    rw [PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.vertexLabels_comp, ih, stepTimeline_vertexLabels]

/-- The actual expanded graph's vertex stages occur in the actual emitted scan-block order. -/
theorem timeline_vertexLabels :
    vertexLabels Prim.interp C.expandedDiagram C.timeline.stage =
      (List.range (scanLength C.environment (List.finRange C.source.edgeCount))).flatMap
        (fun (i : ℕ) => List.replicate
          (vertexList Prim.interp ((C.stepDiagram i).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)).length i) := by
  simp only [expandedDiagram, diagram, timeline, PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.vertexLabels_castLabels,
    PushPuzzle.NCL.Strip.Sweep.TimelineLabeling.vertexLabels_retypeRaw, prefixTimeline_vertexLabels]

/-- Every pair of actual incidences of one expanded edge has uniformly close actual scan stages.
-/
theorem expanded_stage_edge_bounds (u v : C.expandedDiagram.Vtx Prim.interp)
    {p q : WeightedPort C.expandedDiagram.Edge}
    (hp : p ∈ (C.expandedDiagram.graph Prim.interp u).ports)
    (hq : q ∈ (C.expandedDiagram.graph Prim.interp v).ports) (he : p.1.edge = q.1.edge) :
    C.timeline.stage u ≤ C.timeline.stage v + (height K + 1) ∧
      C.timeline.stage v ≤ C.timeline.stage u + (height K + 1) := by
  have hu := C.timeline.localPort u p hp
  have hv := C.timeline.localPort v q hq
  rw [he] at hu
  omega

end PushPuzzle.NCL.Strip.Sweep.Context

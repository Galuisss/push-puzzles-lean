/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StarInverse
public import PushFS.Reduction.GateNeighbors

/-! Exact inverse recovery of source-gate roles from real full-program directed unit queries. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan

private theorem vertex_inside (l : Layer) : 0<l.vertexPoint.2 ∧ l.vertexPoint.2<l.height := by
  dsimp [Layer.vertexPoint,Layer.middleY,Layer.height]
  omega

/-- Every real outgoing unit arc at an actual source gate is exactly one of its creating roles. -/
theorem vertexRecord_outgoing_role {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) {e : ℕ} {d : Direction}
    (ha : HasArc (Route.edgeSegments (refinedProgram w,e)) d (refinePoint v.point)) :
    ∃ role : Fin 3,(v.ports.port role).edge=e ∧ (v.ports.port role).dir=false ∧ d=v.portDirection role := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  obtain ⟨l,row,hl,rfl⟩ := (mem_verticesFrom_iff _ _ _ v).mp hv
  have hn := hl.numbered D (show Numbered ⟨[],0,[]⟩ from ⟨by simp,by simp⟩)
  have hd := hl.drawing D rfl
  rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined,
    hasArc_refined_anchor] at ha
  have hh := hl.arc_inside D rfl (vertex_inside l) ha
  exact l.outgoing_role hn hd hh

/-- Every real incoming unit arc at an actual source gate is exactly one of its consuming roles. -/
theorem vertexRecord_incoming_role {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) {e : ℕ} {d : Direction}
    (ha : HasIncoming (Route.edgeSegments (refinedProgram w,e)) d (refinePoint v.point)) :
    ∃ role : Fin 3,(v.ports.port role).edge=e ∧ (v.ports.port role).dir=true ∧ d=v.portDirection role := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  obtain ⟨l,row,hl,rfl⟩ := (mem_verticesFrom_iff _ _ _ v).mp hv
  have hn := hl.numbered D (show Numbered ⟨[],0,[]⟩ from ⟨by simp,by simp⟩)
  have hd := hl.drawing D rfl
  rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined,
    hasIncoming_refined_anchor] at ha
  have hh := hl.incoming_inside D rfl (vertex_inside l) ha
  exact l.incoming_role hn hd hh

/-- A refined pixel next to an old anchor certifies a true directed unit arm at that same anchor. -/
private theorem Segment.refined_contains_neighbor {s : Segment} {d : Direction}
    {p q : GridRouting.Point}
    (hn : neighbor d (refinePoint q)=some p) (hp : s.refined.Contains p) :
    s.Arc d q ∨ HasIncoming [s] d q := by
  rw [hasIncoming_reversed,List.map_singleton,hasArc_singleton]
  rcases p with ⟨px,py⟩
  cases d <;>
    simp_all [neighbor,Segment.refined,refinePoint,Segment.Contains,Segment.Arc,Segment.reversed] <;> omega

/-- Every actual occupied neighboring pixel belongs to one of the gate's three actual roles. -/
theorem vertexRecord_neighbor_role {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) {e : ℕ} {d : Direction} {p : GridRouting.Point}
    (hn : neighbor d (refinePoint v.point)=some p) (hp : Route.Trace (refinedProgram w) e p) :
    ∃ role : Fin 3,(v.ports.port role).edge=e ∧ d=v.portDirection role := by
  obtain ⟨r,hr,he,s,hs,hp⟩ := hp
  obtain ⟨r',hr',rfl⟩ := List.mem_map.mp hr
  obtain ⟨s',hs',rfl⟩ := List.mem_map.mp hs
  have hmem : s'∈Route.edgeSegments (program w,e) :=
    (Route.mem_edgeSegments _ _ _).mpr ⟨r',hr',he,hs'⟩
  rcases Segment.refined_contains_neighbor hn hp with ha | ha
  · have ha' : HasArc (Route.edgeSegments (refinedProgram w,e)) d (refinePoint v.point) := by
      rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined,hasArc_refined_anchor]
      exact ⟨s',hmem,ha⟩
    obtain ⟨role,hedge,_,hdir⟩ := vertexRecord_outgoing_role hP hT hv ha'
    exact ⟨role,hedge,hdir⟩
  · obtain ⟨q,hq,s'',hs'',ha⟩ := ha
    cases List.mem_singleton.mp hs''
    have ha' : HasIncoming (Route.edgeSegments (refinedProgram w,e)) d (refinePoint v.point) := by
      rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined,hasIncoming_refined_anchor]
      exact ⟨q,hq,s',hmem,ha⟩
    obtain ⟨role,hedge,_,hdir⟩ := vertexRecord_incoming_role hP hT hv ha'
    exact ⟨role,hedge,hdir⟩

namespace Raster

end Raster

end PushPuzzle.PushFS.Reduction

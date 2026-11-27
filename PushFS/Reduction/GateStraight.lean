/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateNeighbors

/-! The first ordinary cell outside each actual source gate is a straight physical wire. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan Gadgets.Wires

/-- One coarse directed unit edge leaves at least fifteen further refined unit edges in the same direction. -/
private theorem Segment.refined_arc_neighbor {s : Segment} {d : Direction} {p q : GridRouting.Point}
    (hn : neighbor d (refinePoint p)=some q) (ha : s.refined.Arc d (refinePoint p)) :
    s.refined.Arc d q := by
  have ho := (s.refined_arc_anchor d p).mp ha
  rcases q with ⟨qx,qy⟩
  cases d <;> simp only [neighbor,refinePoint,Option.some.injEq,Prod.mk.injEq] at hn
  · split_ifs at hn <;> simp_all [Segment.refined,refinePoint,Segment.Arc]; omega
  · dsimp [Segment.refined,refinePoint,Segment.Arc] at ho ⊢
    omega
  · dsimp [Segment.refined,refinePoint,Segment.Arc] at ho ⊢
    omega
  · split_ifs at hn <;> simp_all [Segment.refined,refinePoint,Segment.Arc]; omega

private theorem hasArc_refined_neighbor {ss : List Segment} {d : Direction}
    {p q : GridRouting.Point}
    (hn : neighbor d (refinePoint p)=some q) (ha : HasArc (ss.map Segment.refined) d (refinePoint p)) :
    HasArc (ss.map Segment.refined) d q := by
  obtain ⟨r,hr,ha⟩ := ha
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  exact ⟨s.refined,List.mem_map.mpr ⟨s,hs,rfl⟩,Segment.refined_arc_neighbor hn ha⟩

private theorem hasIncoming_refined_neighbor {ss : List Segment} {d : Direction}
    {p q : GridRouting.Point}
    (hn : neighbor d (refinePoint p)=some q) (ha : HasIncoming (ss.map Segment.refined) d (refinePoint p)) :
    HasIncoming (ss.map Segment.refined) d q := by
  rw [hasIncoming_reversed,map_reversed_refined] at ha ⊢
  exact hasArc_refined_neighbor hn ha

private theorem vertexRecord_neighbor_tangent {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped
    [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) {p : GridRouting.Point}
    (hp : neighbor (v.portDirection role) (refinePoint v.point)=some p) :
    let port := v.ports.port role
    let d := v.portDirection role
    if port.dir then HasIncoming (Route.edgeSegments (refinedProgram w,port.edge)) d p
    else HasArc (Route.edgeSegments (refinedProgram w,port.edge)) d p := by
  have ht := vertexRecord_tangent hP hT hv role
  dsimp only at ht ⊢
  rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined] at ht ⊢
  cases hb : (v.ports.port role).dir
  · simp only [hb,Bool.false_eq_true,ite_false] at ht ⊢
    exact hasArc_refined_neighbor hp ht
  · simp only [hb,ite_true] at ht ⊢
    exact hasIncoming_refined_neighbor hp ht

private theorem straight_checked : ∀ k : Catalog.Kind,
    Catalog.sourceDirection k=Catalog.targetDirection k → k=.east ∨ k=.west ∨ k=.south := by decide +kernel

namespace Raster

/-- Every consuming arm is joined to a straight same-edge wire, through its actual target port. -/
theorem gate_input_straight {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) (hin : (v.ports.port role).dir=true) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      vertexAt (w,p)=none ∧ owner (w,p)=some (v.ports.port role).edge ∧
      wireAt (w,((v.ports.port role).edge,p))=some k ∧
      Catalog.sourceDirection k=(v.portDirection role).opposite ∧
      Catalog.targetDirection k=(v.portDirection role).opposite ∧ (k=.east ∨ k=.west ∨ k=.south) := by
  obtain ⟨p,k,hp,hv',he,hk,hdir⟩ := gate_input_neighbor hP hT hv role hin
  have ht := vertexRecord_neighbor_tangent hP hT hv role hp
  dsimp only at ht
  simp only [hin,ite_true] at ht
  have hsource := wireAt_incoming_direction hk ((incoming_named _ _ _ _).mpr ht)
  exact ⟨p,k,hp,hv',he,hk,hsource,hdir,straight_checked k (hsource.trans hdir.symm)⟩

/-- Every creating arm is joined to a straight same-edge wire, through its actual source port. -/
theorem gate_output_straight {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) (hout : (v.ports.port role).dir=false) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      vertexAt (w,p)=none ∧ owner (w,p)=some (v.ports.port role).edge ∧
      wireAt (w,((v.ports.port role).edge,p))=some k ∧
      Catalog.sourceDirection k=v.portDirection role ∧ Catalog.targetDirection k=v.portDirection role ∧
      (k=.east ∨ k=.west ∨ k=.south) := by
  obtain ⟨p,k,hp,hv',he,hk,hdir⟩ := gate_output_neighbor hP hT hv role hout
  have ht := vertexRecord_neighbor_tangent hP hT hv role hp
  dsimp only at ht
  simp only [hout,Bool.false_eq_true,ite_false] at ht
  have htarget := wireAt_outgoing_direction hk ((outgoing_named _ _ _ _).mpr ht)
  exact ⟨p,k,hp,hv',he,hk,hdir,htarget,straight_checked k (hdir.trans htarget.symm)⟩

end Raster
end PushPuzzle.PushFS.Reduction

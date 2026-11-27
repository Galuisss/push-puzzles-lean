/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StarPorts
public import PushFS.Reduction.CellPlan

/-! Each actual gate role meets an ordinary cell of the same source edge, with the correct physical port. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL Plan Gadgets.Wires

/-- The external source direction selected by this exact source gate record. -/
def Plan.VertexData.portDirection (v : VertexData) (role : Fin 3) : Direction :=
  PortAnnulus.outerDirection (v.annulus.1,v.annulus.2,role)

/-- A new neighbor of an old lattice anchor is always an ordinary refined pixel. -/
private theorem neighbor_refined_ne {d : Direction} {p q r : GridRouting.Point}
    (hn : neighbor d (refinePoint p)=some q) : q≠refinePoint r := by
  intro he
  rw [he] at hn
  cases d <;> simp only [neighbor,refinePoint,Option.some.injEq,Prod.mk.injEq] at hn
  · split_ifs at hn <;> simp_all; omega
  · omega
  · omega
  · split_ifs at hn <;> simp_all; omega

theorem neighbor_refined_vertexAt_none (w : Word) {d : Direction} {p q : GridRouting.Point}
    (hn : neighbor d (refinePoint p)=some q) : Raster.vertexAt (w,q)=none := by
  apply (Raster.vertexAt_none_iff w q).mpr
  rintro ⟨r,_,hr⟩
  exact neighbor_refined_ne hn hr

/-- At the real refined source gate, every selected role has its exact original named directed unit arm. -/
theorem vertexRecord_tangent {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) :
    let port := v.ports.port role
    let d := v.portDirection role
    if port.dir then HasIncoming (Route.edgeSegments (refinedProgram w,port.edge)) d (refinePoint v.point)
    else HasArc (Route.edgeSegments (refinedProgram w,port.edge)) d (refinePoint v.point) := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  obtain ⟨l,row,hl,rfl⟩ := (mem_verticesFrom_iff _ _ _ v).mp hv
  have hn := hl.numbered D (show Numbered ⟨[],0,[]⟩ from ⟨by simp,by simp⟩)
  have hd := hl.drawing D rfl
  have ht := l.annulus_tangent hn hd role
  dsimp only at ht ⊢
  change (if ((orderPorts l.geometricVertex).port role).dir then
    HasIncoming (Route.edgeSegments (refinedProgram w,((orderPorts l.geometricVertex).port role).edge))
      (PortAnnulus.outerDirection (l.annulusKey role)) (refinePoint (l.vertexPoint.1,l.vertexPoint.2+row))
    else HasArc (Route.edgeSegments (refinedProgram w,((orderPorts l.geometricVertex).port role).edge))
      (PortAnnulus.outerDirection (l.annulusKey role)) (refinePoint (l.vertexPoint.1,l.vertexPoint.2+row)))
  rw [show refinedProgram w=(program w).map Route.refined from rfl,Route.edgeSegments_refined]
  cases hb : ((orderPorts l.geometricVertex).port role).dir
  · simp only [hb,Bool.false_eq_true,ite_false] at ht ⊢
    exact (hasArc_refined_anchor _ _ _).mpr (hl.arc ht)
  · simp only [hb,ite_true] at ht ⊢
    exact (hasIncoming_refined_anchor _ _ _).mpr (hl.incoming ht)

namespace Raster

theorem wireAt_incoming_direction {w : Word} {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind}
    (hk : wireAt (w,(e,p))=some k) {d : Direction} (hi : incoming d (w,(e,p))=true) :
    Catalog.sourceDirection k=d.opposite := by
  have hm := (selectWire_correct _ _ k).mp hk
  have hh : (incomingMask (w,(e,p))).get d=true := by simpa only [incomingMask_get] using hi
  rw [hm.1,Mask.single_get] at hh
  have he := congrArg Direction.opposite (of_decide_eq_true hh)
  simpa only [Direction.opposite_opposite] using he.symm

theorem wireAt_outgoing_direction {w : Word} {e : ℕ} {p : GridRouting.Point} {k : Catalog.Kind}
    (hk : wireAt (w,(e,p))=some k) {d : Direction} (ho : outgoing d (w,(e,p))=true) :
    Catalog.targetDirection k=d := by
  have hm := (selectWire_correct _ _ k).mp hk
  have hh : (outgoingMask (w,(e,p))).get d=true := by simpa only [outgoingMask_get] using ho
  rw [hm.2,Mask.single_get] at hh
  exact (of_decide_eq_true hh).symm

/-- A consuming gate arm meets the target of the same original physical wire, in the exact opposite direction. -/
theorem gate_input_neighbor {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) (hin : (v.ports.port role).dir=true) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      vertexAt (w,p)=none ∧ owner (w,p)=some (v.ports.port role).edge ∧
      wireAt (w,((v.ports.port role).edge,p))=some k ∧
      Catalog.targetDirection k=(v.portDirection role).opposite := by
  have ht := vertexRecord_tangent hP hT hv role
  dsimp only at ht
  simp only [hin,ite_true] at ht
  obtain ⟨p,hp,ha⟩ := ht
  have hnone := neighbor_refined_vertexAt_none w hp
  have he := owner_unique hP hT ((vertexAt_none_iff w p).mp hnone)
    ((Route.edgeSegments_trace _ _ _).mp ha.point)
  obtain ⟨k,hk⟩ := wireAt_defined hP hT he hnone
  exact ⟨p,k,hp,hnone,he,hk,wireAt_outgoing_direction hk ((outgoing_named _ _ _ _).mpr ha)⟩

/-- A creating gate arm meets the source of the same original physical wire with the same travel direction. -/
theorem gate_output_neighbor {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {v : VertexData} (hv : v∈vertexRecords w) (role : Fin 3) (hout : (v.ports.port role).dir=false) :
    ∃ p k,neighbor (v.portDirection role) (refinePoint v.point)=some p ∧
      vertexAt (w,p)=none ∧ owner (w,p)=some (v.ports.port role).edge ∧
      wireAt (w,((v.ports.port role).edge,p))=some k ∧
      Catalog.sourceDirection k=v.portDirection role := by
  have ht := vertexRecord_tangent hP hT hv role
  dsimp only at ht
  rw [hout] at ht
  simp only [Bool.false_eq_true,ite_false] at ht
  obtain ⟨p,hp,_,htP⟩ := ht.endpoints
  have hnone := neighbor_refined_vertexAt_none w hp
  have he := owner_unique hP hT ((vertexAt_none_iff w p).mp hnone)
    ((Route.edgeSegments_trace _ _ _).mp htP)
  obtain ⟨k,hk⟩ := wireAt_defined hP hT he hnone
  have hi : incoming (v.portDirection role).opposite (w,((v.ports.port role).edge,p))=true :=
    (incoming_named _ _ _ _).mpr ⟨refinePoint v.point,neighbor_reverse hp,by simpa only [Direction.opposite_opposite] using ht⟩
  exact ⟨p,k,hp,hnone,he,hk,by simpa only [Direction.opposite_opposite] using wireAt_incoming_direction hk hi⟩

end Raster
end PushPuzzle.PushFS.Reduction

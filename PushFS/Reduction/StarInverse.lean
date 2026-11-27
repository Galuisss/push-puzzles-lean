/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StarPorts
public import PushFS.Reduction.LayerInterior
import Mathlib.Data.List.GetD

/-! Complete directed source arcs at a gate recover one of its actual normalized physical roles. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

private theorem Layer.input_no_outgoing {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (i : Fin l.instruction.data.inputs.length) :
    ¬∃ d,HasArc (Route.edgeSegments (l.connections,(l.inputPort i.val).port.edge)) d l.vertexPoint := by
  have hi := i.isLt
  have hk := h.constraints.2.2.1
  have hidx : l.instruction.data.offset+i.val<l.before.wires.length := by omega
  change ¬∃ d,HasArc (Route.edgeSegments (l.connections,l.before.wires.getD (l.instruction.data.offset+i.val) 0)) d _
  rw [l.incoming_segments hn ⟨_,hidx⟩]
  have hf := l.incoming_unitFlow h ⟨l.instruction.data.offset+i.val,hidx⟩
  have hx : l.exitIndex (l.instruction.data.offset+i.val)=none := by
    have hlo : ¬l.instruction.data.offset+i.val<l.instruction.data.offset := by omega
    have hhi : l.instruction.data.offset+i.val<l.instruction.data.offset+l.instruction.data.inputs.length := by omega
    simp only [Layer.exitIndex,hlo,ite_false,hhi,ite_true]
  have hf' : UnitFlow (l.incomingRoute (l.instruction.data.offset+i.val)).path
      (4*(l.instruction.data.offset+i.val),0) l.vertexPoint := by
    simpa only [Layer.incomingTarget,hx,Option.elim_none] using hf
  intro ha
  exact ((hf'.outgoing_iff _).mp ha).2 rfl

private theorem Layer.output_no_incoming {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (i : Fin l.instruction.data.outputs.length) :
    ¬∃ d,HasIncoming (Route.edgeSegments (l.connections,(l.outputPort i.val).port.edge)) d l.vertexPoint := by
  change ¬∃ d,HasIncoming (Route.edgeSegments (l.connections,l.before.next+i.val)) d _
  rw [l.created_segments hn i]
  intro ha
  exact (((l.created_unitFlow h i).incoming_iff _).mp ha).2 rfl

private theorem rotation_onto : ∀ r j : Fin 3,∃ i : Fin 3,(r.val+i.val)%3=j.val := by decide +kernel

/-- Any actual named trace at this source vertex belongs to one of its exact normalized roles. -/
private theorem Layer.vertex_role {l : Layer} (h : l.HasDrawing) {e : ℕ}
    (hp : Route.Trace l.connections e l.vertexPoint) :
    ∃ role : Fin 3,((orderPorts l.geometricVertex).port role).edge=e := by
  obtain ⟨source,hsource,port,hport,he⟩ := l.vertex_port h hp
  obtain ⟨v,hv,hperm⟩ := h.geometric_incidence
  rw [hv,List.mem_singleton] at hsource
  subst source
  have hm := hperm.subset hport
  obtain ⟨j,hj,hget⟩ := List.mem_iff_getElem.mp hm
  have hj' : j<3 := by simpa only [Layer.geometricVertex,l.circularPorts_length h] using hj
  obtain ⟨role,hr⟩ := rotation_onto (portRotation l.geometricVertex) ⟨j,hj'⟩
  refine ⟨role,?_⟩
  rw [l.annulus_port h role]
  change (l.circularPorts.getD (((portRotation l.geometricVertex).val+role.val)%3) ⟨⟨0,false⟩,0⟩).port.edge=e
  rw [hr]
  change j<l.circularPorts.length at hj
  change l.circularPorts[j]=port at hget
  change (l.circularPorts.getD j ⟨⟨0,false⟩,0⟩).port.edge=e
  rw [List.getD_eq_getElem _ _ hj,hget]
  exact he

private theorem Layer.circular_outgoing {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (j : Fin 3)
    {d : Direction}
    (ha : HasArc (Route.edgeSegments (l.connections,(l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port.edge)) d l.vertexPoint) :
    (l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port.dir=false ∧
      d=PortAnnulus.armDirection l.instruction.data.inputs.length
        (PortAnnulus.circularArm l.instruction.data.inputs.length j) := by
  rw [l.circularPort_arm h j] at ha ⊢
  by_cases hi : j.val<l.instruction.data.inputs.length
  · simp only [PortAnnulus.circularArm,hi,ite_true] at ha
    exact False.elim (l.input_no_outgoing hn h ⟨_,hi⟩ ⟨d,ha⟩)
  · have harity := h.constraints.2.1
    have hj := j.isLt
    let i := 3-l.instruction.data.inputs.length-1-(j.val-l.instruction.data.inputs.length)
    have ho : i<l.instruction.data.outputs.length := by dsimp only [i]; omega
    simp only [PortAnnulus.circularArm,hi,ite_false] at ha ⊢
    refine ⟨rfl,?_⟩
    have hf := l.created_unitFlow h ⟨i,ho⟩
    rw [← l.created_segments hn ⟨i,ho⟩] at hf
    exact hf.outgoing_unique l.vertexPoint d _ ha (l.output_tangent hn ⟨i,ho⟩)

private theorem Layer.circular_incoming {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (j : Fin 3)
    {d : Direction}
    (ha : HasIncoming (Route.edgeSegments (l.connections,(l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port.edge)) d l.vertexPoint) :
    (l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port.dir=true ∧
      d=PortAnnulus.armDirection l.instruction.data.inputs.length
        (PortAnnulus.circularArm l.instruction.data.inputs.length j) := by
  rw [l.circularPort_arm h j] at ha ⊢
  by_cases hi : j.val<l.instruction.data.inputs.length
  · simp only [PortAnnulus.circularArm,hi,ite_true] at ha ⊢
    refine ⟨rfl,?_⟩
    have hk := h.constraints.2.2.1
    have hidx : l.instruction.data.offset+j.val<l.before.wires.length := by omega
    have hf := l.incoming_unitFlow h ⟨l.instruction.data.offset+j.val,hidx⟩
    rw [← l.incoming_segments hn ⟨l.instruction.data.offset+j.val,hidx⟩] at hf
    exact hf.incoming_unique l.vertexPoint d _ ha (l.input_tangent hn h ⟨j.val,hi⟩)
  · have harity := h.constraints.2.1
    have hj := j.isLt
    have ho : 3-l.instruction.data.inputs.length-1-(j.val-l.instruction.data.inputs.length)<
        l.instruction.data.outputs.length := by omega
    simp only [PortAnnulus.circularArm,hi,ite_false] at ha
    exact False.elim (l.output_no_incoming hn h ⟨_,ho⟩ ⟨d,ha⟩)

theorem Layer.outgoing_role {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    {e : ℕ} {d : Direction} (ha : HasArc (Route.edgeSegments (l.connections,e)) d l.vertexPoint) :
    ∃ role : Fin 3,((orderPorts l.geometricVertex).port role).edge=e ∧
      ((orderPorts l.geometricVertex).port role).dir=false ∧ d=PortAnnulus.outerDirection (l.annulusKey role) := by
  obtain ⟨role,he⟩ := l.vertex_role h ((Route.edgeSegments_trace _ _ _).mp ha.point)
  have ha' := he.symm ▸ ha
  rw [l.annulus_port h role] at ha'
  have hc := l.circular_outgoing hn h (l.cyclicIndex role) ha'
  exact ⟨role,he,by rw [l.annulus_port h role]; exact hc.1,by rw [l.annulus_direction h role]; exact hc.2⟩

theorem Layer.incoming_role {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    {e : ℕ} {d : Direction} (ha : HasIncoming (Route.edgeSegments (l.connections,e)) d l.vertexPoint) :
    ∃ role : Fin 3,((orderPorts l.geometricVertex).port role).edge=e ∧
      ((orderPorts l.geometricVertex).port role).dir=true ∧ d=PortAnnulus.outerDirection (l.annulusKey role) := by
  obtain ⟨role,he⟩ := l.vertex_role h ((Route.edgeSegments_trace _ _ _).mp ha.point)
  have ha' := he.symm ▸ ha
  rw [l.annulus_port h role] at ha'
  have hc := l.circular_incoming hn h (l.cyclicIndex role) ha'
  exact ⟨role,he,by rw [l.annulus_port h role]; exact hc.1,by rw [l.annulus_direction h role]; exact hc.2⟩

end PushPuzzle.PushFS.Reduction.Plan

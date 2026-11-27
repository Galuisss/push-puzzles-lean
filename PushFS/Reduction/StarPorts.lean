/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerOccurrence

/-! The actual numbered source-star arms have the exact tangent and polarity of their cyclic ports. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem gridStar_input_tangent {a b : ℕ} (i : Fin a) :
    HasIncoming (segments (GridStar.path (Sum.inl i : Fin a ⊕ Fin b)))
      (PortAnnulus.armDirection a ⟨true,i.val⟩) (GridStar.center a,1) := by
  rw [hasIncoming_reversed]
  change HasArc [⟨(i.val,1),(i.val,0)⟩,⟨(GridStar.center a,1),(i.val,1)⟩] _ _
  dsimp only [PortAnnulus.armDirection]
  split_ifs <;> simp_all [HasArc,Segment.Arc]; omega

private theorem gridStar_output_tangent {a b : ℕ} (i : Fin b) :
    HasArc (segments (GridStar.path (Sum.inr i : Fin a ⊕ Fin b)))
      (PortAnnulus.armDirection a ⟨false,i.val⟩) (GridStar.center a,1) := by
  dsimp only [PortAnnulus.armDirection]
  split_ifs <;> simp [HasArc,GridStar.path,segments,Segment.Arc] <;> omega

namespace Plan

theorem Layer.input_tangent {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (i : Fin l.instruction.data.inputs.length) :
    HasIncoming (Route.edgeSegments (l.connections,(l.inputPort i.val).port.edge))
      (PortAnnulus.armDirection l.instruction.data.inputs.length ⟨true,i.val⟩) l.vertexPoint := by
  have hi := i.isLt
  have hk := h.constraints.2.2.1
  have hidx : l.instruction.data.offset+i.val<l.before.wires.length := by omega
  change HasIncoming (Route.edgeSegments (l.connections,l.before.wires.getD (l.instruction.data.offset+i.val) 0)) _ _
  rw [l.incoming_segments hn ⟨_,hidx⟩]
  have hp : ¬l.instruction.data.offset+i.val<l.instruction.data.offset := by omega
  have hg : l.instruction.data.offset+i.val<l.instruction.data.offset+l.instruction.data.inputs.length := by omega
  simp only [Layer.incomingRoute,hp,ite_false,hg,ite_true,Nat.add_sub_cancel_left,hasIncoming_append]
  right
  have hh := gridStar_input_tangent (b:=l.instruction.data.outputs.length) i
  have hh' := (hasIncoming_translate (segments (GridStar.path (Sum.inl i : Fin l.instruction.data.inputs.length ⊕ Fin l.instruction.data.outputs.length)))
      (4*l.instruction.data.offset) l.middleY _ l.vertexPoint).mpr
    ⟨by dsimp [Layer.vertexPoint]; omega,by dsimp [Layer.vertexPoint]; omega,
      by simpa [Layer.vertexPoint] using hh⟩
  simpa [Layer.inputRoutes,List.getD_eq_getElem?_getD,hi,GridStar.path,segments,
    Segment.translate,Layer.vertexPoint,Nat.add_comm] using hh'

theorem Layer.output_tangent {l : Layer} (hn : Numbered l.before)
    (i : Fin l.instruction.data.outputs.length) :
    HasArc (Route.edgeSegments (l.connections,(l.outputPort i.val).port.edge))
      (PortAnnulus.armDirection l.instruction.data.inputs.length ⟨false,i.val⟩) l.vertexPoint := by
  change HasArc (Route.edgeSegments (l.connections,l.before.next+i.val)) _ _
  rw [l.created_segments hn i]
  apply (hasArc_append _ _ _ _).mpr
  left
  have hh := gridStar_output_tangent (a:=l.instruction.data.inputs.length) i
  have hh' := (hasArc_translate (segments (GridStar.path (Sum.inr i : Fin l.instruction.data.inputs.length ⊕ Fin l.instruction.data.outputs.length)))
      (4*l.instruction.data.offset) l.middleY _ l.vertexPoint).mpr
    ⟨by dsimp [Layer.vertexPoint]; omega,by dsimp [Layer.vertexPoint]; omega,
      by simpa [Layer.vertexPoint] using hh⟩
  simpa [Layer.createdRoute,Layer.outputRoutes,List.getD_eq_getElem?_getD,i.isLt,GridStar.path,segments,
    Segment.translate,Layer.vertexPoint,Nat.add_comm] using hh'

/-- Every geometric cyclic slot carries its own exact source edge, tangent and input/output polarity. -/
private theorem Layer.circular_tangent {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing)
    (j : Fin 3) :
    let port := (l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port
    let d := PortAnnulus.armDirection l.instruction.data.inputs.length
      (PortAnnulus.circularArm l.instruction.data.inputs.length j)
    if port.dir then HasIncoming (Route.edgeSegments (l.connections,port.edge)) d l.vertexPoint
    else HasArc (Route.edgeSegments (l.connections,port.edge)) d l.vertexPoint := by
  dsimp only
  rw [l.circularPort_arm h j]
  by_cases hi : j.val<l.instruction.data.inputs.length
  · simp only [PortAnnulus.circularArm,hi,ite_true,Layer.inputPort]
    exact l.input_tangent hn h ⟨j.val,hi⟩
  · have ha := h.constraints.2.1
    have hj := j.isLt
    have ho : 3-l.instruction.data.inputs.length-1-(j.val-l.instruction.data.inputs.length)<
        l.instruction.data.outputs.length := by omega
    simp only [PortAnnulus.circularArm,hi,ite_false,Layer.outputPort]
    exact l.output_tangent hn ⟨_,ho⟩

/-- The actual annulus role has the same directed unit arm as the original numbered source star. -/
theorem Layer.annulus_tangent {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing) (role : Fin 3) :
    let port := (orderPorts l.geometricVertex).port role
    let d := PortAnnulus.outerDirection (l.annulusKey role)
    if port.dir then HasIncoming (Route.edgeSegments (l.connections,port.edge)) d l.vertexPoint
    else HasArc (Route.edgeSegments (l.connections,port.edge)) d l.vertexPoint := by
  dsimp only
  rw [l.annulus_port h role,l.annulus_direction h role]
  exact l.circular_tangent hn h (l.cyclicIndex role)

end Plan
end PushPuzzle.PushFS.Reduction

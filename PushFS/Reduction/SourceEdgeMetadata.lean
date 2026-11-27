/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.CompleteFlow
public import PushFS.Reduction.SourcePortExact

/-! Exact source-edge endpoint records and distinct normalized roles of every real placed gate. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan

open Cslib.Complexity.NCL
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

private theorem circular_edges_injective {l : Layer} (hn : Numbered l.before) (h : l.HasDrawing) :
    Function.Injective (fun j : Fin 3=>(l.circularPorts.getD j.val ⟨⟨0,false⟩,0⟩).port.edge) := by
  intro i j he
  dsimp only at he
  rw [l.circularPort_arm h i,l.circularPort_arm h j] at he
  have hi:=i.isLt
  have hj:=j.isLt
  have harity:=h.constraints.2.1
  by_cases hI : i.val<l.instruction.data.inputs.length
  · by_cases hJ : j.val<l.instruction.data.inputs.length
    · simp only [PortAnnulus.circularArm,hI,hJ,ite_true] at he
      have hh:=l.input_edges_injective hn h (a₁:=⟨i.val,hI⟩) (a₂:=⟨j.val,hJ⟩) he
      exact Fin.ext (congrArg (fun x : Fin l.instruction.data.inputs.length=>x.val) hh)
    · simp only [PortAnnulus.circularArm,hI,hJ,Bool.false_eq_true,ite_true,ite_false] at he
      exact False.elim (l.input_ne_output hn h ⟨i.val,hI⟩ ⟨_,by omega⟩ he)
  · by_cases hJ : j.val<l.instruction.data.inputs.length
    · simp only [PortAnnulus.circularArm,hI,hJ,Bool.false_eq_true,ite_true,ite_false] at he
      exact False.elim (l.input_ne_output hn h ⟨j.val,hJ⟩ ⟨_,by omega⟩ he.symm)
    · simp only [PortAnnulus.circularArm,hI,hJ,Bool.false_eq_true,ite_false] at he
      have hh:=l.output_edges_injective (a₁:=⟨3-l.instruction.data.inputs.length-1-(i.val-l.instruction.data.inputs.length),by omega⟩) (a₂:=⟨3-l.instruction.data.inputs.length-1-(j.val-l.instruction.data.inputs.length),by omega⟩) he
      apply Fin.ext
      have heq : 3-l.instruction.data.inputs.length-1-(i.val-l.instruction.data.inputs.length)=
          3-l.instruction.data.inputs.length-1-(j.val-l.instruction.data.inputs.length):=
        congrArg (fun x : Fin l.instruction.data.outputs.length=>x.val) hh
      omega

private theorem cyclic_injective (l : Layer) : Function.Injective l.cyclicIndex := by
  have h : ∀a b c : Fin 3,(a.val+b.val)%3=(a.val+c.val)%3→b=c := by decide +kernel
  intro i j he
  exact h (portRotation l.geometricVertex) i j (congrArg Fin.val he)

/-- All three physical roles at an actual gate have distinct original source edges. -/
theorem vertexRecord_edges_injective {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {g : VertexData} (hg : g∈vertexRecords w) :
    Function.Injective (fun r : Fin 3=>(g.ports.port r).edge) := by
  obtain ⟨D⟩:=Word.orthogonalDrawing hP hT
  obtain ⟨l,y,hl,rfl⟩:=(mem_verticesFrom_iff _ _ _ g).mp hg
  have hd:=hl.drawing D rfl
  have hn:=hl.numbered D (show Numbered ⟨[],0,[]⟩ from ⟨by simp,by simp⟩)
  intro r s he
  change ((orderPorts l.geometricVertex).port r).edge=((orderPorts l.geometricVertex).port s).edge at he
  rw [l.annulus_port hd r,l.annulus_port hd s] at he
  exact cyclic_injective l (circular_edges_injective hn hd he)

theorem OutputEndpoint.record {w : Word} {e : ℕ} {p : GridRouting.Point}
    (hp : OutputEndpoint w ⟨[],0,[]⟩ 0 e p) : ∃g∈vertexRecords w,g.point=p :=
  List.mem_map.mp ((mem_vertexPoints_iff _ _ _ _).mpr hp.vertex)

theorem InputEndpoint.record {w : Word} {e : ℕ} {p : GridRouting.Point}
    (hp : InputEndpoint w ⟨[],0,[]⟩ 0 e p) : ∃g∈vertexRecords w,g.point=p :=
  List.mem_map.mp ((mem_vertexPoints_iff _ _ _ _).mpr hp.vertex)

/-- A true source-edge unit step at its emitted output recovers that original gate's creating role. -/
theorem OutputEndpoint.role {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {p : GridRouting.Point} (hp : OutputEndpoint w ⟨[],0,[]⟩ 0 e p)
    {d : Direction} (ha : HasArc (Route.edgeSegments (refinedProgram w,e)) d (refinePoint p)) :
    ∃g∈vertexRecords w,∃r : Fin 3,g.point=p ∧(g.ports.port r).edge=e ∧
      (g.ports.port r).dir=false ∧d=g.portDirection r := by
  obtain ⟨g,hg,hpoint⟩:=hp.record
  have ha':HasArc (Route.edgeSegments (refinedProgram w,e)) d (refinePoint g.point):=hpoint.symm ▸ha
  obtain ⟨r,he,hi,hd⟩:=vertexRecord_outgoing_role hP hT hg ha'
  exact ⟨g,hg,r,hpoint,he,hi,hd⟩

/-- A true final predecessor at its emitted input recovers that original gate's consuming role. -/
theorem InputEndpoint.role {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {p : GridRouting.Point} (hp : InputEndpoint w ⟨[],0,[]⟩ 0 e p)
    {d : Direction} (ha : HasIncoming (Route.edgeSegments (refinedProgram w,e)) d (refinePoint p)) :
    ∃g∈vertexRecords w,∃r : Fin 3,g.point=p ∧(g.ports.port r).edge=e ∧
      (g.ports.port r).dir=true ∧d=g.portDirection r := by
  obtain ⟨g,hg,hpoint⟩:=hp.record
  have ha':HasIncoming (Route.edgeSegments (refinedProgram w,e)) d (refinePoint g.point):=hpoint.symm ▸ha
  obtain ⟨r,he,hi,hd⟩:=vertexRecord_incoming_role hP hT hg ha'
  exact ⟨g,hg,r,hpoint,he,hi,hd⟩

/-- A source edge has no other actual gate at an internal unit-flow pixel. -/
theorem vertexRecord_not_internal {w : Word} (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {e : ℕ} {g : VertexData} (hg : g∈vertexRecords w)
    {di do_ : Direction}
    (hi : HasIncoming (Route.edgeSegments (refinedProgram w,e)) di (refinePoint g.point))
    (ho : HasArc (Route.edgeSegments (refinedProgram w,e)) do_ (refinePoint g.point)) : False := by
  obtain ⟨r,he,hr,_⟩:=vertexRecord_incoming_role hP hT hg hi
  obtain ⟨s,hf,hs,_⟩:=vertexRecord_outgoing_role hP hT hg ho
  have hrs: r=s:=vertexRecord_edges_injective hP hT hg (he.trans hf.symm)
  rw [hrs,hs] at hr
  cases hr
end PushPuzzle.PushFS.Reduction.Plan

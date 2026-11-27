/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.NamedSegments
public import PushFS.Reduction.SegmentJoins
import Mathlib.Data.List.GetD

/-! Full directed-unit contracts for the actual cut-to-cut and vertex-to-cut source programs. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL

private theorem Layer.upper_unitFlow (l : Layer) (i : Fin l.before.wires.length) :
    UnitFlow (Band.curve (l.upperBand,i.val)) (4*i.val,0)
      (expanded l.instruction.data.offset l.instruction.data.inputs.length i.val,l.middleY) := by
  have hlen : l.upperBand.source.length=l.before.wires.length := by simp [Layer.upperBand]
  have h := l.upperBand.unitFlow ⟨i.val,by rw [hlen]; exact i.isLt⟩
  simpa [Layer.upperBand,Layer.middleY,Band.sourceColumn,Band.targetColumn,
    List.getD_eq_getElem?_getD,i.isLt] using h

private theorem Layer.lower_unitFlow (l : Layer) (i : Fin l.after.wires.length) :
    UnitFlow (l.bottomPath i.val)
      (expanded l.instruction.data.offset l.instruction.data.outputs.length i.val,l.middleY+2)
      (4*i.val,l.height) := by
  have hlen : l.lowerBand.source.length=l.after.wires.length := by simp [Layer.lowerBand]
  have h := (l.lowerBand.unitFlow ⟨i.val,by rw [hlen]; exact i.isLt⟩).translate 0 (l.middleY+2)
  simpa [Layer.bottomPath,Layer.lowerBand,Layer.middleY,Layer.height,Band.sourceColumn,Band.targetColumn,
    List.getD_eq_getElem?_getD,i.isLt,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using h

private theorem Layer.strand_connects (l : Layer) (e : l.Strand) :
    Connects (l.strandRoute e).path
      ((GridLayout.middleStart e).1,(GridLayout.middleStart e).2+l.middleY)
      ((GridLayout.middleEnd e).1,(GridLayout.middleEnd e).2+l.middleY) := by
  rw [l.strandRoute_path]
  change Connects (segments ((GridLayout.middlePath e).translate 0 l.middleY)) _ _
  rw [segments_translate]
  have h : Connects (segments (GridLayout.middlePath e)) (GridLayout.middleStart e) (GridLayout.middleEnd e) := ⟨_,rfl⟩
  simpa only [Nat.add_zero] using h.translate 0 l.middleY

private theorem Layer.strand_top_unique (l : Layer) (e : l.Strand) (h0 :
    (GridLayout.middleStart e).2=0)
    {p : GridRouting.Point} (hp : HasPoint (l.strandRoute e).path p) (hy : p.2=l.middleY) :
    p=((GridLayout.middleStart e).1,l.middleY) := by
  rw [l.strandRoute_path] at hp
  change HasPoint (segments ((GridLayout.middlePath e).translate 0 l.middleY)) p at hp
  rw [segments_translate] at hp
  obtain ⟨_,_,hp⟩ := (hasPoint_translate _ 0 l.middleY p).mp hp
  have he := middle_top_unique e h0 hp (by dsimp only; omega)
  have hx := congrArg Prod.fst he
  apply Prod.ext
  · simpa only [Nat.sub_zero] using hx
  · exact hy

private theorem Layer.lower_top_unique (l : Layer) (i : Fin l.after.wires.length)
    {p : GridRouting.Point}
    (hp : HasPoint (l.bottomPath i.val) p) (hy : p.2=l.middleY+2) :
    p=(expanded l.instruction.data.offset l.instruction.data.outputs.length i.val,l.middleY+2) := by
  have hlen : l.lowerBand.source.length=l.after.wires.length := by simp [Layer.lowerBand]
  obtain ⟨_,_,hp⟩ := (hasPoint_translate _ 0 (l.middleY+2) p).mp hp
  have hx := l.lowerBand.curve_top ⟨i.val,by rw [hlen]; exact i.isLt⟩ _ (by dsimp only; omega) hp
  apply Prod.ext
  · simpa [Layer.lowerBand,List.getD_eq_getElem?_getD,i.isLt] using hx
  · exact hy

/-- Every incoming source connection has one true unit predecessor and successor at each internal pixel. -/
theorem Layer.incoming_unitFlow {l : Layer} (h : l.HasDrawing) (i : Fin l.before.wires.length) :
    UnitFlow (l.incomingRoute i.val).path (4*i.val,0) (l.incomingTarget i.val) := by
  let ss := Band.curve (l.upperBand,i.val)
  let tt := (l.strandRoute (l.topStrand i)).path
  let q : GridRouting.Point :=
    ((GridLayout.middleEnd (l.topStrand i)).1,(GridLayout.middleEnd (l.topStrand i)).2+l.middleY)
  have hs := l.upper_unitFlow i
  have hcS := l.upper_connects i
  have ht := l.strand_unitFlow (l.topStrand i)
  have hcT := l.strand_connects (l.topStrand i)
  rw [l.topStrand_start i] at ht hcT
  simp only [Nat.zero_add] at ht hcT
  have h0 : (GridLayout.middleStart (l.topStrand i)).2=0 := by rw [l.topStrand_start i]
  have huniq : ∀ p,HasPoint tt p → p.2=l.middleY →
      p=(expanded l.instruction.data.offset l.instruction.data.inputs.length i.val,l.middleY) := by
    intro p hp hy
    have hh := l.strand_top_unique (l.topStrand i) h0 hp hy
    simpa only [l.topStrand_start i] using hh
  have hf : UnitFlow (ss++tt) (4*i.val,0) q := hs.append_at_row ht hcS hcT huniq
  have hc : Connects (ss++tt) (4*i.val,0) q := hcS.append hcT
  have hfull := l.incoming_connects h i
  cases hx : l.exitIndex i.val with
  | none =>
    have hpath : (l.incomingRoute i.val).path=ss++tt := by
      rw [l.incoming_decompose i,hx]
      simp only [ss,tt,Option.elim_none,List.append_nil]
    rw [hpath] at hfull
    have he := (hc.endpoints_unique hfull).2
    rw [hpath]
    exact he ▸ hf
  | some j =>
    have hj := l.exitIndex_lt h i.isLt hx
    have hl := l.lower_unitFlow ⟨j,hj⟩
    have hcL := l.lower_connects ⟨j,hj⟩
    have hpath : (l.incomingRoute i.val).path=(ss++tt)++l.bottomPath j := by
      rw [l.incoming_decompose i,hx]
      simp only [ss,tt,Option.elim_some,List.append_assoc]
    rw [hpath] at hfull
    have he := hfull.append_contact hc hcL
    have hf' : UnitFlow (ss++tt) (4*i.val,0)
        (expanded l.instruction.data.offset l.instruction.data.outputs.length j,l.middleY+2) := he ▸ hf
    have hc' : Connects (ss++tt) (4*i.val,0)
        (expanded l.instruction.data.offset l.instruction.data.outputs.length j,l.middleY+2) := he ▸ hc
    have hh := hf'.append_at_row hl hc' hcL (fun p hp hy=>l.lower_top_unique ⟨j,hj⟩ hp hy)
    rw [hpath]
    simpa only [Layer.incomingTarget,hx,Option.elim_some] using hh

/-- Every newly emitted source edge begins at the actual source vertex and follows a true unit path to its cut. -/
theorem Layer.created_unitFlow {l : Layer} (h : l.HasDrawing) (i : Fin l.instruction.data.outputs.length) :
    UnitFlow (l.createdRoute i.val).path l.vertexPoint
      (4*(l.instruction.data.offset+i.val),l.height) := by
  let e : l.Strand := .inr (.inl (.inr i))
  let ss := (l.outputRoutes.getD i.val ⟨0,[]⟩).path
  let q : GridRouting.Point := (4*l.instruction.data.offset+i.val,l.middleY+2)
  have hs : UnitFlow ss l.vertexPoint q := by
    simpa [e,ss,q,Layer.strandRoute,GridLayout.middleStart,GridLayout.middleEnd,
      Layer.vertexPoint,Nat.add_comm] using l.strand_unitFlow e
  have hcS : Connects ss l.vertexPoint q := by
    simpa [e,ss,q,Layer.strandRoute,GridLayout.middleStart,GridLayout.middleEnd,
      Layer.vertexPoint,Nat.add_comm] using l.strand_connects e
  have hi := l.outputIndex_lt h i
  have ht := l.lower_unitFlow ⟨l.instruction.data.offset+i.val,hi⟩
  have hcT := l.lower_connects ⟨l.instruction.data.offset+i.val,hi⟩
  have hfull := l.created_connects h i
  have he := hfull.append_contact hcS hcT
  have hs' : UnitFlow ss l.vertexPoint
      (expanded l.instruction.data.offset l.instruction.data.outputs.length (l.instruction.data.offset+i.val),l.middleY+2) := he ▸ hs
  have hcS' : Connects ss l.vertexPoint
      (expanded l.instruction.data.offset l.instruction.data.outputs.length (l.instruction.data.offset+i.val),l.middleY+2) := he ▸ hcS
  exact hs'.append_at_row ht hcS' hcT (fun p hp hy=>l.lower_top_unique ⟨_,hi⟩ hp hy)

end PushPuzzle.PushFS.Reduction.Plan

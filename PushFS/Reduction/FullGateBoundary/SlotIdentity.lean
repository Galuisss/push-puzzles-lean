/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateBoundary.LineSlots

/-! Complete canonical source and target identity classification throughout the actual outer inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

open Inventory
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def SourceIdentity (g : GateTileState) (f : Direction) : (i : Index g)→Labels g i→Prop
  | .inr (.inl ⟨role,.inl j⟩),l =>
    j.val+1=(curve (key g role)).length ∧PortAnnulus.outerDirection (g.key role).2=f ∧
    ((l=lineLast (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
          (filler_shape (key g role) j.val j.isLt).2.1 ∧
        lineSourcePoint (key g role) j (initialPhase g role) (targetPhase g role) l=
          endpointPoint f (g.incoming.get role) (initialPhase g role) false) ∨
      ((g.incoming.get role=true ∨initialPhase g role=true) ∧
        l=linePenultimate (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
          (filler_shape (key g role) j.val j.isLt).2.1 ∧
        lineSourcePoint (key g role) j (initialPhase g role) (targetPhase g role) l=
          endpointPoint f (g.incoming.get role) (initialPhase g role) true))
  | .inl _,_ | .inr (.inl ⟨_,.inr _⟩),_ | .inr (.inr _),_ => False

def TargetIdentity (g : GateTileState) (f : Direction) : (i : Index g)→Labels g i→Prop
  | .inr (.inl ⟨role,.inl j⟩),l =>
    j.val+1=(curve (key g role)).length ∧PortAnnulus.outerDirection (g.key role).2=f ∧
    ((l=lineLast (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
          (filler_shape (key g role) j.val j.isLt).2.1 ∧
        lineTargetPoint (key g role) j (initialPhase g role) (targetPhase g role) l=
          endpointPoint f (g.incoming.get role) (targetPhase g role) false) ∨
      ((g.incoming.get role=true ∨targetPhase g role=true) ∧
        l=linePenultimate (fillerFlip (key g role) j.val) (fillerSpan (key g role) j.val)
          (filler_shape (key g role) j.val j.isLt).2.1 ∧
        lineTargetPoint (key g role) j (initialPhase g role) (targetPhase g role) l=
          endpointPoint f (g.incoming.get role) (targetPhase g role) true))
  | .inl _,_ | .inr (.inl ⟨_,.inr _⟩),_ | .inr (.inr _),_ => False

theorem source_identity (g : GateTileState) (f : Direction) (i : Index g) (l : Labels g i)
    (hf : InFrame f ((offset g i).1+((matching g i).source l).1.val,
      (offset g i).2+((matching g i).source l).2.val)) : SourceIdentity g f i l := by
  have ho:=raw_owner g i f ((matching g i).source l) hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact ho.elim
  · obtain ⟨hj,hd⟩:=ho
    refine ⟨hj,hd,?_⟩
    have hd' : PortAnnulus.outerDirection (key g role).1.2=f := hd
    have hh:=last_source_frame (key g role) j hj (initialPhase g role) (targetPhase g role) l (by rwa [hd'])
    convert hh using 1 <;> simp only [key,hd] <;> rfl
  · exact ho.elim
  · exact l.elim0

theorem target_identity (g : GateTileState) (f : Direction) (i : Index g) (l : Labels g i)
    (hf : InFrame f ((offset g i).1+((matching g i).target l).1.val,
      (offset g i).2+((matching g i).target l).2.val)) : TargetIdentity g f i l := by
  have ho:=raw_owner g i f ((matching g i).target l) hf
  rcases i with i | (⟨role,j | j⟩ | role)
  · exact ho.elim
  · obtain ⟨hj,hd⟩:=ho
    refine ⟨hj,hd,?_⟩
    have hd' : PortAnnulus.outerDirection (key g role).1.2=f := hd
    have hh:=last_target_frame (key g role) j hj (initialPhase g role) (targetPhase g role) l (by rwa [hd'])
    convert hh using 1 <;> simp only [key,hd] <;> rfl
  · exact ho.elim
  · exact l.elim0

end PushPuzzle.PushFS.Reduction.GateTileRouting.FullGateBoundary

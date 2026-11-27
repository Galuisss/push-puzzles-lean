/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusArmSignals
public import PushFS.Reduction.FullGateBoundary.LineSlots

/-! The real annular far signal reads the literal full-gate outer endpoint box and its exact boundary threshold. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation cornerIso lineOrientation

def outerLine (g : GateTileState) (r : Fin 3) : Fin (curve (key g r)).length :=
  ⟨(curve (key g r)).length-1,by have:=frontier_first_valid (key g r); omega⟩

private theorem outerLine_last (g : GateTileState) (r : Fin 3) : (outerLine g r).val+1=(curve
    (key g r)).length := by
  have:=frontier_first_valid (key g r)
  change (curve (key g r)).length-1+1=(curve (key g r)).length
  omega

def outerEndpointLabel (g : GateTileState) (r : Fin 3) : RawLabel g :=lineEndpointLabel g r (outerLine g r) true

def outerEndpointCell (d : Direction) (incoming a : Bool) : C :=
  (⟨(FullGateBoundary.endpointPoint d incoming a false).1,by cases d <;> cases incoming <;> cases a <;> decide⟩,
    ⟨(FullGateBoundary.endpointPoint d incoming a false).2,by cases d <;> cases incoming <;> cases a <;> decide⟩)

def outerAnchor (g : GateTileState) (r : Fin 3) : C :=
  outerEndpointCell (PortAnnulus.outerDirection (g.key r).2) (g.incoming.get r) true

private theorem outer_travel (g : GateTileState) (r : Fin 3) :
    (original (key g r) (outerLine g r).val).travel=PortAnnulus.outerDirection (g.key r).2 :=
  (FullGateBoundary.last_line_metadata (key g r) (outerLine g r) (outerLine_last g r)).2.1

theorem outer_source_coordinates (g : GateTileState) (r : Fin 3) :
    (((rawSlotMatching g).source (outerEndpointLabel g r)).1.val,
      ((rawSlotMatching g).source (outerEndpointLabel g r)).2.val)=
      FullGateBoundary.endpointPoint (PortAnnulus.outerDirection (g.key r).2) (g.incoming.get r) (initialPhase g r) false := by
  let j:=outerLine g r
  have hs:=raw_source g (.inr (.inl ⟨r,.inl j⟩))
    (lineLast (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1)
  exact (congrArg (fun p : C=>(p.1.val,p.2.val)) hs).trans
    (FullGateBoundary.last_source_endpoint (key g r) j (outerLine_last g r) (initialPhase g r) (targetPhase g r) false)

private theorem outer_reference (g : GateTileState) (r : Fin 3) :
    lineReference (key g r) (outerLine g r).val (outerLine g r).isLt (initialPhase g r) (targetPhase g r) true=
      outerAnchor g r := by
  let j:=outerLine g r
  have href:=line_reference_coordinates (key g r) j.val j.isLt (initialPhase g r) (targetPhase g r) true
  have hsource:=line_endpoint_coordinates (key g r) j.val j.isLt true true true
  have hout:=FullGateBoundary.last_source_endpoint (key g r) j (outerLine_last g r) true true false
  have hxy:=href.trans (hsource.symm.trans hout)
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {g : GateTileState}

def OuterHigh (image : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height) (r : Fin 3) : Prop :=
  let p:=image.point (outerAnchor g r)
  let q:=S.position (image.labels (outerEndpointLabel g r))
  TravelHigh (PortAnnulus.outerDirection (g.key r).2) (p.1.val,p.2.val) (q.1.val,q.2.val)

theorem arm_to_outer (image : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height) (r : Fin 3)
    (hin : LineHigh image S r (outerLine g r) true) : OuterHigh image S r := by
  have hpoint:=congrArg image.point (outer_reference g r)
  have hphase:=(congrArg (fun p : Cell I.width I.height=>TravelHigh (original (key g r) (outerLine g r).val).travel
    (p.1.val,p.2.val) ((S.position (image.labels (outerEndpointLabel g r))).1.val,
      (S.position (image.labels (outerEndpointLabel g r))).2.val)) hpoint).mp hin
  exact (congrArg (fun d=>TravelHigh d
    ((image.point (outerAnchor g r)).1.val,(image.point (outerAnchor g r)).2.val)
    ((S.position (image.labels (outerEndpointLabel g r))).1.val,(S.position (image.labels (outerEndpointLabel g r))).2.val))
    (outer_travel g r)).mp hphase

end PushPuzzle.PushFS.Reduction.GateTileRouting

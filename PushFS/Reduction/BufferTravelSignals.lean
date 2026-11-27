/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.BufferImages

/-! Successful physical paths transmit each true core inward threshold through its complete buffered lead. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires Catalog Soundness Gates.Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

def coreEndpointLabel (g : GateTileState) (r : Fin 3) : RawLabel g :=
  ⟨.inl 0,Relay.outerLabel g.core.isAND r⟩

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {g : GateTileState}

noncomputable def coreAnchor (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) : Cell I.width I.height :=
  image.point ((coreEmbedding g).cells (coreGhost g.core.isAND r))

def CoreHigh (image : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height) (r : Fin 3) : Prop :=
  TravelHigh (Gates.portDirection r) ((coreAnchor image r).1.val,(coreAnchor image r).2.val)
    ((S.position (image.labels (coreEndpointLabel g r))).1.val,(S.position (image.labels (coreEndpointLabel g r))).2.val)

def BufferHigh (image : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height)
    (r : Fin 3) (last : Bool) : Prop :=
  let lead:=image.comp (bufferImage g r)
  let anchor:=lead.orientedPoint (frontierOrientation g.core.isAND r)
    (if last then chainTargetAnchor 2301 else chainSourceAnchor 2301)
  let label:=lead.labels (if last then Polyline.ChainEnds.last 2301 (by omega) else Polyline.ChainEnds.first 2301 (by omega))
  TravelHigh (Gates.portDirection r) (anchor.1.val,anchor.2.val) ((S.position label).1.val,(S.position label).2.val)

private theorem coreEndpoint_source (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    M.source (image.labels (coreEndpointLabel g r))=
      image.point ((coreEmbedding g).cells (Gates.position g.core.isAND g.core.initial (Relay.outerLabel g.core.isAND r))) :=
  (image.sources _).trans (congrArg image.point (raw_source g (.inl 0) (Relay.outerLabel g.core.isAND r)))

private theorem buffer_ghost_point (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    (image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r) (chainGhost 2301)=coreAnchor image r := by
  exact (StorageImage.comp_orientedPoint _ image (bufferImage g r) _).trans
    (congrArg image.point ((bufferImage_point g r _).trans (buffer_ghost g r).symm))

private theorem buffer_component (image : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (l : Chain.Label 2301) :
    component I.board (M.source (image.labels (coreEndpointLabel g r)))=
      component I.board (M.source ((image.comp (bufferImage g r)).labels l)) := by
  have hc:=buffer_source_component g r l
  have hp : SameComponent I.board
      (image.point ((rawSlotMatching g).source (coreEndpointLabel g r)))
      (image.point ((rawSlotMatching g).source (bufferLabel g r l))) :=
    ⟨GridEmbedding.staticReach image.walls hc.1,GridEmbedding.staticReach image.walls hc.2⟩
  have he : (image.comp (bufferImage g r)).labels l=image.labels (bufferLabel g r l) :=
    congrArg image.labels (bufferImage_labels g r l)
  rw [he,image.sources,image.sources]
  exact component_eq_iff.mpr hp

private theorem core_anchor_step (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    (Inventory.initialPhase g r=true→M.source (image.labels (coreEndpointLabel g r))=coreAnchor image r) ∧
      (Inventory.initialPhase g r=false→Adjacent (Gates.portDirection r)
        (M.source (image.labels (coreEndpointLabel g r))) (coreAnchor image r)) := by
  have hc:=core_ghost_step g.core.isAND g.core.initial r
  constructor
  · intro h
    exact (coreEndpoint_source image r).trans (congrArg (fun p=>image.point ((coreEmbedding g).cells p)) (hc.1 h))
  · intro h
    have ha:=image.point_adjacent ((coreEmbedding g).adjacent _ _ _ (hc.2 h))
    exact (coreEndpoint_source image r).symm ▸ha

private theorem chain_first_point (a : Bool) :
    Chain.position 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.first 2301 (by omega))=
      if a then chainSourceAnchor 2301 else ((2,10):Chain.C 2301) := by
  have hx:=Polyline.ChainEnds.first_x 2301 (by omega) a
  have hy:=Chain.position_row 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.first 2301 (by omega))
  cases a <;> apply Prod.ext <;> apply Fin.ext
  all_goals first | exact hx | exact hy

private theorem buffer_first_source (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    M.source ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.first 2301 (by omega)))=
      (image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r)
        (if Inventory.initialPhase g r then chainSourceAnchor 2301 else ((2,10):Chain.C 2301)) := by
  have he:=(image.comp (bufferImage g r)).sources (Polyline.ChainEnds.first 2301 (by omega))
  exact he.trans (congrArg ((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r))
    (chain_first_point (Inventory.initialPhase g r)))

private theorem buffer_reference_step (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    DirectionalStep (Gates.portDirection r) ((coreAnchor image r).1.val,(coreAnchor image r).2.val)
      (((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r) (chainSourceAnchor 2301)).1.val,
        ((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r) (chainSourceAnchor 2301)).2.val) := by
  let lead:=image.comp (bufferImage g r)
  let o:=frontierOrientation g.core.isAND r
  have h1:=lead.orientedPoint_adjacent o (show Adjacent .east (chainGhost 2301) ((2,10):Chain.C 2301) from ⟨rfl,rfl⟩)
  have h2:=lead.orientedPoint_adjacent o (show Adjacent .east ((2,10):Chain.C 2301) (chainSourceAnchor 2301) from ⟨rfl,rfl⟩)
  have hh:=adjacent_twice h1 h2
  change DirectionalStep ((frontierOrientation g.core.isAND r).direction .east) _ _ at hh
  rw [frontier_outward,buffer_ghost_point] at hh
  exact hh

private theorem buffer_source_step (image : StorageImage M (rawSlotMatching g)) (r : Fin 3) :
    DirectionalStep (Gates.portDirection r)
      ((M.source (image.labels (coreEndpointLabel g r))).1.val,(M.source (image.labels (coreEndpointLabel g r))).2.val)
      ((M.source ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.first 2301 (by omega)))).1.val,
        (M.source ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.first 2301 (by omega)))).2.val) := by
  have hfirst:=buffer_first_source image r
  by_cases hp : Inventory.initialPhase g r=false
  · have hz : (if Inventory.initialPhase g r then chainSourceAnchor 2301 else ((2,10):Chain.C 2301))=
        ((2,10):Chain.C 2301) := ite_eq_right (by rw [hp]; decide)
    have hf:=hfirst.trans (congrArg ((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r)) hz)
    have hcore:=(core_anchor_step image r).2 hp
    have hnext:=(image.comp (bufferImage g r)).orientedPoint_adjacent (frontierOrientation g.core.isAND r)
      (show Adjacent .east (chainGhost 2301) ((2,10):Chain.C 2301) from ⟨rfl,rfl⟩)
    rw [frontier_outward,buffer_ghost_point] at hnext
    exact adjacent_twice hcore (hf.symm ▸hnext)
  · have hp' : Inventory.initialPhase g r=true:=Bool.eq_true_of_not_eq_false hp
    have hz : (if Inventory.initialPhase g r then chainSourceAnchor 2301 else ((2,10):Chain.C 2301))=
        chainSourceAnchor 2301 := ite_eq_left hp'
    have hf:=hfirst.trans (congrArg ((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r)) hz)
    have hcore:=(core_anchor_step image r).1 hp'
    have hh:=buffer_reference_step image r
    exact hcore.symm ▸hf.symm ▸hh

private theorem step_order (d : Direction) (p q : ℕ×ℕ) (h : DirectionalStep d p q) : DirectionalOrder d p q := by
  cases d <;> dsimp only [DirectionalStep,DirectionalOrder] at * <;> omega

theorem core_to_buffer_signal (image : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : CoreHigh image S r) : BufferHigh image S r true := by
  let lead:=image.comp (bufferImage g r)
  let o:=frontierOrientation g.core.isAND r
  have horder : DirectionalOrder (Gates.portDirection r)
      ((M.source (image.labels (coreEndpointLabel g r))).1.val,(M.source (image.labels (coreEndpointLabel g r))).2.val)
      ((M.source (lead.labels (Polyline.ChainEnds.first 2301 (by omega)))).1.val,
        (M.source (lead.labels (Polyline.ChainEnds.first 2301 (by omega)))).2.val) := by
    exact step_order _ _ _ (buffer_source_step image r)
  have hgap:=directional_gap (Gates.portDirection r) hs cert (image.labels (coreEndpointLabel g r))
    (lead.labels (Polyline.ChainEnds.first 2301 (by omega))) (buffer_component image r _) horder
  have hnear:=travelHigh_join (Gates.portDirection r) _ _ _ _ (buffer_reference_step image r) hgap hin
  have hout:=rotated_chain_signal 2301 (by omega) (Inventory.initialPhase g r) (Inventory.targetPhase g r)
    o lead hs cert ordered (by simpa only [o,lead,frontier_outward] using hnear)
  change TravelHigh (Gates.portDirection r)
    ((lead.orientedPoint o (chainTargetAnchor 2301)).1.val,(lead.orientedPoint o (chainTargetAnchor 2301)).2.val)
    ((S.position (lead.labels (Polyline.ChainEnds.last 2301 (by omega)))).1.val,
      (S.position (lead.labels (Polyline.ChainEnds.last 2301 (by omega)))).2.val)
  simpa only [o,lead,frontier_outward] using hout

end PushPuzzle.PushFS.Reduction.GateTileRouting

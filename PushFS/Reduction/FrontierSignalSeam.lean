/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.BufferTravelSignals
public import PushFS.Reduction.AnnulusArmSignals

/-! The actual buffered lead's far signal crosses the shared first annular-line anchor. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation cornerIso lineOrientation

private theorem placed_eq_of_relative {w h v z : ℕ} (o : RectOrientation) (dx dy ex ey : ℕ)
    (p a : Cell w h) (q b : Cell v z)
    (ha : o.coordinates w h dx dy a=o.coordinates v z ex ey b)
    (hr : ((p.1.val:ℤ)-a.1.val,(p.2.val:ℤ)-a.2.val)=((q.1.val:ℤ)-b.1.val,(q.2.val:ℤ)-b.2.val)) :
    o.coordinates w h dx dy p=o.coordinates v z ex ey q := by
  have hv:=congrArg o.vector hr
  rw [←o.cells_difference w h p a,←o.cells_difference v z q b] at hv
  have hx:=congrArg Prod.fst hv
  have hy:=congrArg Prod.snd hv
  have hax:=congrArg Prod.fst ha
  have hay:=congrArg Prod.snd ha
  dsimp only [RectOrientation.coordinates] at hax hay
  apply Prod.ext <;> dsimp only [RectOrientation.coordinates]
  · omega
  · omega

private theorem frontier_corresponding (g : GateTileState) (r : Fin 3) (a b : Bool)
    (p : Chain.C 2301)
    (q : Cell (lineBase (fillerFlip (key g r) 0) (fillerSpan (key g r) 0)
      (filler_shape (key g r) 0 (frontier_first_valid _)).2.1 a b).width
      (lineBase (fillerFlip (key g r) 0) (fillerSpan (key g r) 0)
        (filler_shape (key g r) 0 (frontier_first_valid _)).2.1 a b).height)
    (hx : p.1.val=2301+q.1.val) (hy : p.2.val=q.2.val) :
    (frontierOrientation g.core.isAND r).coordinates 2306 21
      (frontierBufferOffset g r).1 (frontierBufferOffset g r).2 p=
      (frontierOrientation g.core.isAND r).coordinates _ _ (lineOffset (key g r) 0).1 (lineOffset (key g r) 0).2 q := by
  apply placed_eq_of_relative _ _ _ _ _ p (frontierLeadAnchor 2301) q (lineNearAnchor _ _ _ a b)
    (frontier_shared_anchor g r a b)
  apply Prod.ext <;> dsimp only [frontierLeadAnchor,lineNearAnchor] <;> omega

private theorem bufferImage_coordinates (g : GateTileState) (r : Fin 3) (p : Chain.C 2301) :
    (((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) p).1.val,
      ((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) p).2.val)=
      (frontierOrientation g.core.isAND r).coordinates 2306 21
        (frontierBufferOffset g r).1 (frontierBufferOffset g r).2 p := by
  rcases g with ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  fin_cases r <;> cases kind <;> rfl

def frontierGhost (a : Bool) : Chain.C 2301 := (⟨2303+a.toNat,by cases a <;> decide⟩,10)

private theorem frontier_source_ghost (g : GateTileState) (r : Fin 3) :
    (bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (frontierGhost (initialPhase g r))=
      rawSource g (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false) := by
  let k:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  let f:=fillerFlip k 0
  let n:=fillerSpan k 0
  let hn:2301≤n:=(filler_shape k 0 (frontier_first_valid _)).2.1
  let p:=(lineMatching f n hn a b).source (lineFirst f n hn)
  have hp:=line_first_position f n hn a b
  change p.1.val=2+a.toNat ∧p.2.val=10 at hp
  have hc:=frontier_corresponding g r a b (frontierGhost a) p (by change 2303+a.toNat=2301+p.1.val; omega) (by exact hp.2.symm)
  have hl:=line_source_coordinates k 0 (frontier_first_valid _) a b (lineFirst f n hn)
  rw [frontier_first_orientation] at hl
  have hxy:=(bufferImage_coordinates g r (frontierGhost a)).trans (hc.trans hl.symm)
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

private theorem frontier_reference_ghost (g : GateTileState) (r : Fin 3) :
    (bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (frontierGhost true)=
      lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false := by
  let k:=key g r
  let a:=initialPhase g r
  let b:=targetPhase g r
  let f:=fillerFlip k 0
  let n:=fillerSpan k 0
  let hn:2301≤n:=(filler_shape k 0 (frontier_first_valid _)).2.1
  let p:=lineThresholdCell f n hn a b false
  have hc:=frontier_corresponding g r a b (frontierGhost true) p (by rfl) (by rfl)
  have hl: (frontierOrientation g.core.isAND r).coordinates _ _ (lineOffset k 0).1 (lineOffset k 0).2 p=
      ((lineReference k 0 (frontier_first_valid _) a b false).1.val,
        (lineReference k 0 (frontier_first_valid _) a b false).2.val) := by
    have ho:=frontier_first_orientation k
    exact congrArg (fun o : RectOrientation=>o.coordinates _ _ (lineOffset k 0).1 (lineOffset k 0).2 p) ho.symm
  have hxy:=(bufferImage_coordinates g r (frontierGhost true)).trans (hc.trans hl)
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst hxy
  · exact congrArg Prod.snd hxy

private theorem matching_source (g : GateTileState) (l : RawLabel g) : (rawSlotMatching g).source l=rawSource g l := by
  rcases l with ⟨i,l⟩
  exact raw_source g i l

theorem frontier_source_component (g : GateTileState) (r : Fin 3) :
    SameComponent (fullPuzzle g).board
      ((rawSlotMatching g).source (bufferLabel g r (Polyline.ChainEnds.last 2301 (by omega))))
      ((rawSlotMatching g).source (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false)) := by
  let a:=initialPhase g r
  let b:=targetPhase g r
  have hw : (bufferLeadEmbedding g r).WallsAgree (lineBase false 2301 (by omega) a b).board (fullPuzzle g).board := by
    intro p
    exact buffer_lead_walls g r p
  have hc:=line_exit_component false 2301 (by omega) a b
  have hp : SameComponent (fullPuzzle g).board
      ((bufferLeadEmbedding g r).cells (Chain.position 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.last 2301 (by omega))))
      ((bufferLeadEmbedding g r).cells (frontierGhost a)) :=
    ⟨GridEmbedding.staticReach hw hc.1,GridEmbedding.staticReach hw hc.2⟩
  have he : (bufferLeadEmbedding g r).cells (frontierGhost a)=
      (rawSlotMatching g).source (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false) :=
    (bufferImage_point g r _).symm.trans ((frontier_source_ghost g r).trans (matching_source g _).symm)
  apply component_eq_iff.mp
  exact (congrArg (component (fullPuzzle g).board) (bufferLabel_source g r _)).trans
    ((component_eq_iff.mpr hp).trans (congrArg (component (fullPuzzle g).board) he))

private theorem buffer_last_point (a : Bool) :
    Chain.position 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.last 2301 (by omega))=
      ((⟨2301+a.toNat,by cases a <;> decide⟩,10):Chain.C 2301) :=
  Prod.ext (Fin.ext (Polyline.ChainEnds.last_x 2301 (by omega) a)) (Fin.ext (Chain.position_row 2301 (by omega) _ _))

private theorem frontier_source_step (g : GateTileState) (r : Fin 3) :
    DirectionalStep (Gates.portDirection r)
      ((((rawSlotMatching g).source (bufferLabel g r (Polyline.ChainEnds.last 2301 (by omega))))).1.val,
        (((rawSlotMatching g).source (bufferLabel g r (Polyline.ChainEnds.last 2301 (by omega))))).2.val)
      ((((rawSlotMatching g).source (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false))).1.val,
        (((rawSlotMatching g).source (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false))).2.val) := by
  let a:=initialPhase g r
  let middle : Chain.C 2301:=(⟨2302+a.toNat,by cases a <;> decide⟩,10)
  have h1 : Adjacent .east (Chain.position 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.last 2301 (by omega))) middle := by
    rw [buffer_last_point]
    refine ⟨?_,rfl⟩
    change 2302+a.toNat=2301+a.toNat+1
    omega
  have h2 : Adjacent .east middle (frontierGhost a) := by
    refine ⟨?_,rfl⟩
    change 2303+a.toNat=2302+a.toNat+1
    omega
  have hstep:=adjacent_twice ((bufferImage g r).orientedPoint_adjacent (frontierOrientation g.core.isAND r) h1)
    ((bufferImage g r).orientedPoint_adjacent (frontierOrientation g.core.isAND r) h2)
  rw [frontier_outward,frontier_source_ghost] at hstep
  have hsource : (rawSlotMatching g).source (bufferLabel g r (Polyline.ChainEnds.last 2301 (by omega)))=
      (bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r)
        (Chain.position 2301 (by omega) (Chain.uniform 2301 a) (Polyline.ChainEnds.last 2301 (by omega))) :=
    (bufferLabel_source g r _).trans (bufferImage_point g r _).symm
  rw [←hsource,←matching_source g (lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false)] at hstep
  exact hstep

private theorem frontier_reference_step (g : GateTileState) (r : Fin 3) :
    DirectionalStep (Gates.portDirection r)
      (((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301)).1.val,
        ((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301)).2.val)
      ((lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false).1.val,
        (lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false).2.val) := by
  have h1:Adjacent .east (chainTargetAnchor 2301) ((2303,10):Chain.C 2301):=⟨rfl,rfl⟩
  have h2:Adjacent .east ((2303,10):Chain.C 2301) (frontierGhost true):=⟨rfl,rfl⟩
  have hstep:=adjacent_twice ((bufferImage g r).orientedPoint_adjacent (frontierOrientation g.core.isAND r) h1)
    ((bufferImage g r).orientedPoint_adjacent (frontierOrientation g.core.isAND r) h2)
  rw [frontier_outward,frontier_reference_ghost] at hstep
  exact hstep

private theorem frontier_first_travel (g : GateTileState) (r : Fin 3) :
    (original (key g r) 0).travel=Gates.portDirection r := by
  have hd:=congrArg (fun o : RectOrientation=>o.direction .east) (frontier_first_orientation (key g r))
  rw [line_direction,frontier_outward] at hd
  exact hd

private theorem step_order (d : Direction) (p q : ℕ×ℕ) (h : DirectionalStep d p q) : DirectionalOrder d p q := by
  cases d <;> dsimp only [DirectionalStep,DirectionalOrder] at * <;> omega

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {g : GateTileState}

private theorem buffer_to_first_line (image : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I)
    (hin : BufferHigh image S r true) : LineHigh image S r ⟨0,frontier_first_valid _⟩ false := by
  let i:=bufferLabel g r (Polyline.ChainEnds.last 2301 (by omega))
  let j:=lineEndpointLabel g r ⟨0,frontier_first_valid _⟩ false
  have hcomp:=image.source_component i j (frontier_source_component g r)
  have horder:=image.source_directional_order (Gates.portDirection r) i j (step_order _ _ _ (frontier_source_step g r))
  have hgap:=directional_gap (Gates.portDirection r) hs cert (image.labels i) (image.labels j) hcomp horder
  have href:=image.directional_step (Gates.portDirection r)
    ((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301))
    (lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false) (frontier_reference_step g r)
  have hlabels : (image.comp (bufferImage g r)).labels (Polyline.ChainEnds.last 2301 (by omega))=image.labels i :=
    congrArg image.labels (bufferImage_labels g r _)
  have hpoint:=StorageImage.comp_orientedPoint (frontierOrientation g.core.isAND r) image (bufferImage g r) (chainTargetAnchor 2301)
  change TravelHigh (Gates.portDirection r)
    (((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301)).1.val,
      ((image.comp (bufferImage g r)).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301)).2.val)
    ((S.position ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.last 2301 (by omega)))).1.val,
      (S.position ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.last 2301 (by omega)))).2.val) at hin
  have hin':=(congrArg (fun p : Cell I.width I.height=>TravelHigh (Gates.portDirection r) (p.1.val,p.2.val)
    ((S.position ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.last 2301 (by omega)))).1.val,
      (S.position ((image.comp (bufferImage g r)).labels (Polyline.ChainEnds.last 2301 (by omega)))).2.val)) hpoint).mp hin
  have hin'':=(congrArg (fun l : L=>TravelHigh (Gates.portDirection r)
    ((image.point ((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301))).1.val,
      (image.point ((bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) (chainTargetAnchor 2301))).2.val)
    ((S.position l).1.val,(S.position l).2.val)) hlabels).mp hin'
  have hout:=travelHigh_join (Gates.portDirection r) _ _ _ _ href hgap hin''
  exact (congrArg (fun d=>TravelHigh d
    ((image.point (lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false)).1.val,
      (image.point (lineReference (key g r) 0 (frontier_first_valid _) (initialPhase g r) (targetPhase g r) false)).2.val)
    ((S.position (image.labels j)).1.val,(S.position (image.labels j)).2.val)) (frontier_first_travel g r)).mpr hout

theorem buffer_to_arm (image : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    {S T : LabelledState L I.width I.height} (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : BufferHigh image S r true) :
    LineHigh image S r ⟨(curve (key g r)).length-1,by have:=frontier_first_valid (key g r); omega⟩ true :=
  arm_signal image r hs cert ordered (buffer_to_first_line image r hs cert hin)

end PushPuzzle.PushFS.Reduction.GateTileRouting

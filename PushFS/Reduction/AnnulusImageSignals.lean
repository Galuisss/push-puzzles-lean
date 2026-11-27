/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusReferences
public import PushFS.Reduction.PhysicalImages
public import PushFS.Gadgets.Wires.Catalog.StoragePoints

/-! Actual annular source identities, true reference thresholds and local successful-path signals in any full-gate image. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Inventory Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] curve original cornerKind cornerOrientation lineOrientation

variable {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L} {g : GateTileState}

noncomputable def signalPoint (f : StorageImage M (rawSlotMatching g)) (p : C) : Cell I.width I.height :=
  (GridEmbedding.translate f.dx f.dy f.fit_x f.fit_y).cells p

noncomputable def lineImage (f : StorageImage M (rawSlotMatching g)) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    StorageImage M (lineSlotMatching (key g r) j.val j.isLt (initialPhase g r) (targetPhase g r)) :=
  f.comp (primitiveRawImage g (.inr (.inl ⟨r,.inl j⟩)))

noncomputable def cornerImage (f : StorageImage M (rawSlotMatching g)) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    StorageImage M (cornerMatching (key g r) j.val (initialPhase g r) (targetPhase g r)) :=
  f.comp (primitiveRawImage g (.inr (.inl ⟨r,.inr j⟩)))

private theorem lineImage_threshold (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin (curve (key g r)).length) (last : Bool) :
    lineThreshold (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
      (initialPhase g r) (targetPhase g r) (original (key g r) j.val).travel (lineImage f r j) last=
      signalPoint f (lineReference (key g r) j.val j.isLt (initialPhase g r) (targetPhase g r) last) := by
  exact StorageImage.comp_orientedPoint _ f (primitiveRawImage g (.inr (.inl ⟨r,.inl j⟩)))
    (lineThresholdCell (fillerFlip (key g r) j.val) (fillerSpan (key g r) j.val) (filler_shape (key g r) j.val j.isLt).2.1
      (initialPhase g r) (targetPhase g r) last)

theorem cornerImage_threshold (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) (last : Bool) :
    ShortCorners.thresholdCell (cornerKind (key g r) j.val) (cornerOrientation (key g r) j.val)
      (initialPhase g r) (targetPhase g r) (cornerImage f r j)
      (if last then ShortCorners.last (cornerKind (key g r) j.val) else ShortCorners.first (cornerKind (key g r) j.val))=
      signalPoint f (cornerReference (key g r) j.val (by have:=j.isLt; omega) last) := by
  exact StorageImage.comp_orientedPoint _ f (primitiveRawImage g (.inr (.inl ⟨r,.inr j⟩)))
    ((ShortCorners.template (cornerKind (key g r) j.val)).position true
      (if last then ShortCorners.last (cornerKind (key g r) j.val) else ShortCorners.first (cornerKind (key g r) j.val)))

def LineHigh (f : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height)
    (r : Fin 3) (j : Fin (curve (key g r)).length) (last : Bool) : Prop :=
  let p:=signalPoint f (lineReference (key g r) j.val j.isLt (initialPhase g r) (targetPhase g r) last)
  let q:=S.position (f.labels (lineEndpointLabel g r j last))
  TravelHigh (original (key g r) j.val).travel (p.1.val,p.2.val) (q.1.val,q.2.val)

def CornerHigh (f : StorageImage M (rawSlotMatching g)) (S : LabelledState L I.width I.height)
    (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) (last : Bool) : Prop :=
  let p:=signalPoint f (cornerReference (key g r) j.val (by have:=j.isLt; omega) last)
  let q:=S.position (f.labels (cornerEndpointLabel g r j last))
  TravelHigh (original (key g r) (if last then j.val+1 else j.val)).travel (p.1.val,p.2.val) (q.1.val,q.2.val)

theorem line_image_signal (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin (curve (key g r)).length) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : LineHigh f S r j false) : LineHigh f S r j true := by
  let q:=key g r
  let flip:=fillerFlip q j.val
  let n:=fillerSpan q j.val
  let hn:2301≤n:=(filler_shape q j.val j.isLt).2.1
  let a:=initialPhase g r
  let b:=targetPhase g r
  let d:=(original q j.val).travel
  let image:=lineImage f r j
  have hi : TravelHigh d ((lineThreshold flip n hn a b d image false).1.val,
      (lineThreshold flip n hn a b d image false).2.val)
      ((S.position (image.labels (lineFirst flip n hn))).1.val,(S.position (image.labels (lineFirst flip n hn))).2.val) := by
    rw [lineImage_threshold]
    exact hin
  have ht:=(lineHigh_iff_travel flip n hn a b d image true _).mp
    (line_signal flip n hn a b d image hs cert ordered ((lineHigh_iff_travel flip n hn a b d image false _).mpr hi))
  rw [lineImage_threshold] at ht
  exact ht

theorem corner_image_signal (f : StorageImage M (rawSlotMatching g)) (r : Fin 3)
    (j : Fin ((curve (key g r)).length-1)) {S T : LabelledState L I.width I.height}
    (hs : Successful M S T) (cert : Certificate I) (ordered : M.Ordered)
    (hin : CornerHigh f S r j false) : CornerHigh f S r j true := by
  let q:=key g r
  let k:=cornerKind q j.val
  let o:=cornerOrientation q j.val
  let a:=initialPhase g r
  let b:=targetPhase g r
  let image:=cornerImage f r j
  have hd : o.direction .west=(original q j.val).travel ∧o.direction .south=(original q (j.val+1)).travel := by
    exact corner_directions q j.val (by have hj:j.val<(curve q).length-1:=j.isLt; omega)
  have hi : TravelHigh (o.direction .west)
      ((ShortCorners.thresholdCell k o a b image (ShortCorners.first k)).1.val,
        (ShortCorners.thresholdCell k o a b image (ShortCorners.first k)).2.val)
      ((S.position (image.labels (ShortCorners.first k))).1.val,(S.position (image.labels (ShortCorners.first k))).2.val) := by
    have hpoint:=cornerImage_threshold f r j false
    simp only [Bool.false_eq_true,ite_false] at hpoint
    apply (congrArg (fun p : Cell I.width I.height=>TravelHigh (o.direction .west) (p.1.val,p.2.val)
      ((S.position (image.labels (ShortCorners.first k))).1.val,(S.position (image.labels (ShortCorners.first k))).2.val)) hpoint).mpr
    exact (congrArg (fun d=>TravelHigh d
      ((signalPoint f (cornerReference q j.val (by have hj:j.val<(curve q).length-1:=j.isLt; omega) false)).1.val,
        (signalPoint f (cornerReference q j.val (by have hj:j.val<(curve q).length-1:=j.isLt; omega) false)).2.val)
      ((S.position (image.labels (ShortCorners.first k))).1.val,(S.position (image.labels (ShortCorners.first k))).2.val)) hd.1).mpr hin
  have hout:=ShortCorners.travel_signal k o a b image hs cert ordered hi
  have hpoint:=cornerImage_threshold f r j true
  simp only [ite_true] at hpoint
  have hout':=(congrArg (fun p : Cell I.width I.height=>TravelHigh (o.direction .south) (p.1.val,p.2.val)
    ((S.position (image.labels (ShortCorners.last k))).1.val,(S.position (image.labels (ShortCorners.last k))).2.val)) hpoint).mp hout
  exact (congrArg (fun d=>TravelHigh d
    ((signalPoint f (cornerReference q j.val (by have hj:j.val<(curve q).length-1:=j.isLt; omega) true)).1.val,
      (signalPoint f (cornerReference q j.val (by have hj:j.val<(curve q).length-1:=j.isLt; omega) true)).2.val)
    ((S.position (image.labels (ShortCorners.last k))).1.val,(S.position (image.labels (ShortCorners.last k))).2.val)) hd.2).mp hout'

end PushPuzzle.PushFS.Reduction.GateTileRouting

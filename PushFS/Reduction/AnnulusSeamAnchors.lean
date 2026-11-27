/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusInventory
public import PushFS.Reduction.AnnulusShortOwners

/-! Actual physical source/target coordinates and shared anchors of the annular storage inventory. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

theorem line_source_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q i) (fillerSpan q i)) :
    ((lineOffset q i).1+((lineSlotMatching q i hi a b).source l).1.val,
      (lineOffset q i).2+((lineSlotMatching q i hi a b).source l).2.val)=
      (lineOrientation (original q i).travel (fillerFlip q i)).coordinates
        (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
        (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height
        (lineOffset q i).1 (lineOffset q i).2
        ((lineMatching (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).source l) := rfl

theorem line_target_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool)
    (l : lineLabels (fillerFlip q i) (fillerSpan q i)) :
    ((lineOffset q i).1+((lineSlotMatching q i hi a b).target l).1.val,
      (lineOffset q i).2+((lineSlotMatching q i hi a b).target l).2.val)=
      (lineOrientation (original q i).travel (fillerFlip q i)).coordinates
        (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
        (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height
        (lineOffset q i).1 (lineOffset q i).2
        ((lineMatching (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).target l) := rfl

theorem corner_source_coordinates (q : Key) (i : ℕ) (a b : Bool)
    (l : Fin (ShortCorners.count (cornerKind q i))) :
    ((cornerOffset q i).1+((cornerMatching q i a b).source l).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).source l).2.val)=
      (cornerOrientation q i).coordinates (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))
        (cornerOffset q i).1 (cornerOffset q i).2 ((ShortCorners.template (cornerKind q i)).position a l) := rfl

theorem corner_target_coordinates (q : Key) (i : ℕ) (a b : Bool)
    (l : Fin (ShortCorners.count (cornerKind q i))) :
    ((cornerOffset q i).1+((cornerMatching q i a b).target l).1.val,
      (cornerOffset q i).2+((cornerMatching q i a b).target l).2.val)=
      (cornerOrientation q i).coordinates (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))
        (cornerOffset q i).1 (cornerOffset q i).2 ((ShortCorners.template (cornerKind q i)).position b l) := rfl

set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem line_anchors_checked : ∀ q : Key,∀ i : Fin (curve q).length,
    let o := lineOrientation (original q i.val).travel (fillerFlip q i.val)
    let w := lineWidth q i.val
    let start := o.point w 21 (2,10)
    let finish := o.point w 21 ((filler q i.val).span+2,10)
    ((lineOffset q i.val).1+start.1,(lineOffset q i.val).2+start.2)=fillerStart q i.val ∧
    ((lineOffset q i.val).1+finish.1,(lineOffset q i.val).2+finish.2)=fillerEnd q i.val := by decide +kernel

theorem line_near_anchor_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    (lineOrientation (original q i).travel (fillerFlip q i)).coordinates
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height
      (lineOffset q i).1 (lineOffset q i).2
      (lineNearAnchor (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b)=fillerStart q i := by
  rw [RectOrientation.coordinates_point]
  dsimp only [lineNearAnchor]
  rw [(line_dimensions (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).1,
    (line_dimensions (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).2]
  exact (line_anchors_checked q ⟨i,hi⟩).1

theorem line_far_anchor_coordinates (q : Key) (i : ℕ) (hi : i<(curve q).length) (a b : Bool) :
    (lineOrientation (original q i).travel (fillerFlip q i)).coordinates
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).width
      (lineBase (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).height
      (lineOffset q i).1 (lineOffset q i).2
      (lineFarAnchor (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b)=fillerEnd q i := by
  rw [RectOrientation.coordinates_point]
  dsimp only [lineFarAnchor]
  rw [(line_dimensions (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).1,
    (line_dimensions (fillerFlip q i) (fillerSpan q i) (filler_shape q i hi).2.1 a b).2]
  have hs : fillerSpan q i+(if fillerFlip q i then 20 else 0)=(filler q i).span := by
    have hh := (filler_shape q i hi).2.2.1
    cases hf : fillerFlip q i <;> simpa [hf] using hh
  rw [hs]
  exact (line_anchors_checked q ⟨i,hi⟩).2

theorem corner_near_anchor_coordinates (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    (cornerOrientation q i).coordinates (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))
      (cornerOffset q i).1 (cornerOffset q i).2 (ShortCorners.nearAnchor (cornerKind q i))=fillerEnd q i :=
  (corner_anchors q i hi).1

theorem corner_far_anchor_coordinates (q : Key) (i : ℕ) (hi : i+1<(curve q).length) :
    (cornerOrientation q i).coordinates (ShortCorners.width (cornerKind q i)) (ShortCorners.height (cornerKind q i))
      (cornerOffset q i).1 (cornerOffset q i).2 (ShortCorners.farAnchor (cornerKind q i))=fillerStart q (i+1) :=
  (corner_anchors q i hi).2

end PushPuzzle.PushFS.Reduction.GateTileRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateProfiles
public import PushFS.Reduction.AnnulusSeamWalkingGeometry
public import PushFS.Reduction.AnnulusShortContacts

/-! Exact shared walking cells of every real neighboring long filler and protected corner. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

private theorem lineBaseCorner_native (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (i : Fin 4) :
    lineBaseCorner flip n hn a b i=nativeLineCorner flip n hn a b i := by cases flip <;> rfl

private theorem near_portal_coordinates (q : Key) (j : ℕ) (hj : j+1<(curve q).length) (a b : Bool) :
    (lineOrientation (original q j).travel (fillerFlip q j)).coordinates _ _
      (lineOffset q j).1 (lineOffset q j).2
      (nativeLineCorner (fillerFlip q j) (fillerSpan q j) (filler_shape q j (by omega)).2.1 a b
        (nearSeamCorner (turnDirections q j).1 (turnDirections q j).2 (fillerFlip q j)))=
    (cornerOrientation q j).coordinates _ _ (cornerOffset q j).1 (cornerOffset q j).2
      (ShortCorners.nearPortal (cornerKind q j)) := by
  have ha:=(line_far_anchor_coordinates q j (by omega) a b).trans (corner_near_anchor_coordinates q j hj).symm
  exact near_seam_corner (turn_perpendicular q j hj) (fillerFlip q j) (fillerSpan q j) (filler_shape q j (by omega)).2.1
    a b (lineOffset q j).1 (lineOffset q j).2 (cornerOffset q j).1 (cornerOffset q j).2 ha

private theorem far_portal_coordinates (q : Key) (j : ℕ) (hj : j+1<(curve q).length) (a b : Bool) :
    (lineOrientation (original q (j+1)).travel (fillerFlip q (j+1))).coordinates _ _
      (lineOffset q (j+1)).1 (lineOffset q (j+1)).2
      (nativeLineCorner (fillerFlip q (j+1)) (fillerSpan q (j+1)) (filler_shape q (j+1) hj).2.1 a b
        (farSeamCorner (turnDirections q j).1 (turnDirections q j).2))=
    (cornerOrientation q j).coordinates _ _ (cornerOffset q j).1 (cornerOffset q j).2
      (ShortCorners.farPortal (cornerKind q j)) := by
  have ha:=(line_near_anchor_coordinates q (j+1) hj a b).trans (corner_far_anchor_coordinates q j hj).symm
  exact far_seam_corner_any (turn_perpendicular q j hj) (fillerFlip q (j+1)) (later_line_unflipped q j)
    (fillerSpan q (j+1)) (filler_shape q (j+1) hj).2.1 a b
    (lineOffset q (j+1)).1 (lineOffset q (j+1)).2 (cornerOffset q j).1 (cornerOffset q j).2 ha

def previousLine (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) : Fin (curve (key g r)).length :=
  ⟨j.val,by have:=j.isLt; omega⟩

def followingLine (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) : Fin (curve (key g r)).length :=
  ⟨j.val+1,by have:=j.isLt; omega⟩

def incomingSeamCorner (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) : Fin 4 :=
  nearSeamCorner (turnDirections (key g r) j.val).1 (turnDirections (key g r) j.val).2 (fillerFlip (key g r) j.val)

def outgoingSeamCorner (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) : Fin 4 :=
  farSeamCorner (turnDirections (key g r) j.val).1 (turnDirections (key g r) j.val).2

/-- The real incoming filler corner and the protected turn's incoming portal are one actual board cell. -/
theorem incoming_seam_cell (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    (lineEmbedding g r (previousLine g r j)).cells
      (lineCorner g r (previousLine g r j) (incomingSeamCorner g r j))=
      (armCornerEmbedding g r j).cells (ShortCorners.nearPortal (cornerKind (key g r) j.val)) := by
  have hh:=near_portal_coordinates (key g r) j.val (by have:=j.isLt; omega)
    (Inventory.initialPhase g r) (Inventory.targetPhase g r)
  rw [←lineBaseCorner_native] at hh
  have hline:=line_coordinates g r (previousLine g r j) (lineCorner g r (previousLine g r j) (incomingSeamCorner g r j))
  have hcorner : (((armCornerEmbedding g r j).cells (ShortCorners.nearPortal (cornerKind (key g r) j.val))).1.val,
      ((armCornerEmbedding g r j).cells (ShortCorners.nearPortal (cornerKind (key g r) j.val))).2.val)=
      (cornerOrientation (key g r) j.val).coordinates _ _ (cornerOffset (key g r) j.val).1 (cornerOffset (key g r) j.val).2
        (ShortCorners.nearPortal (cornerKind (key g r) j.val)) := rfl
  have he:=hline.trans (hh.trans hcorner.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

/-- The real outgoing filler corner and the protected turn's outgoing portal are one actual board cell. -/
theorem outgoing_seam_cell (g : GateTileState) (r : Fin 3) (j : Fin ((curve (key g r)).length-1)) :
    (lineEmbedding g r (followingLine g r j)).cells
      (lineCorner g r (followingLine g r j) (outgoingSeamCorner g r j))=
      (armCornerEmbedding g r j).cells (ShortCorners.farPortal (cornerKind (key g r) j.val)) := by
  have hh:=far_portal_coordinates (key g r) j.val (by have:=j.isLt; omega)
    (Inventory.initialPhase g r) (Inventory.targetPhase g r)
  rw [←lineBaseCorner_native] at hh
  have hline:=line_coordinates g r (followingLine g r j) (lineCorner g r (followingLine g r j) (outgoingSeamCorner g r j))
  have hcorner : (((armCornerEmbedding g r j).cells (ShortCorners.farPortal (cornerKind (key g r) j.val))).1.val,
      ((armCornerEmbedding g r j).cells (ShortCorners.farPortal (cornerKind (key g r) j.val))).2.val)=
      (cornerOrientation (key g r) j.val).coordinates _ _ (cornerOffset (key g r) j.val).1 (cornerOffset (key g r) j.val).2
        (ShortCorners.farPortal (cornerKind (key g r) j.val)) := rfl
  have he:=hline.trans (hh.trans hcorner.symm)
  exact Prod.ext (Fin.ext (congrArg Prod.fst he)) (Fin.ext (congrArg Prod.snd he))

end PushPuzzle.PushFS.Reduction.GateTileRouting

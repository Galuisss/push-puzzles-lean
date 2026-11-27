/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusCorners
public import PushFS.Reduction.AnnulusLineEndpoints
public import PushFS.RectVector

/-! Actual short-turn box identities are separated from the complete canonical neighboring long-line intervals. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

def nearRelative (d e : Direction) (flip : Bool) (p : ℤ×ℤ) : ℤ×ℤ :=
  (lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector
    (p.1-(ShortCorners.sourceX (cornerKindFor d e) : ℤ),p.2-10))

def farRelative (d e : Direction) (p : ℤ×ℤ) : ℤ×ℤ :=
  (lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector
    (p.1-10,p.2-(ShortCorners.lastY (cornerKindFor d e)+2 : ℕ)))

def shortSlotCoordinates (k : ShortCorners.Kind) (a : Bool) (l : Fin (ShortCorners.count k)) : ℤ×ℤ :=
  (((ShortCorners.template k).position a l).1.val,((ShortCorners.template k).position a l).2.val)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- Every true short-turn slot on the incoming rail lies at or beyond its phase-shifted input anchor. -/
theorem short_near_slots : ∀ (d e : Direction) (flip a : Bool) (l : Fin (ShortCorners.count (cornerKindFor d e))),
    RectOrientation.Perpendicular d e →
    (nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).2=0 →
      (a.toNat : ℤ)≤(nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).1 := by
  decide +kernel

/-- Every true short-turn slot on the outgoing rail lies two travel cells before the next line's same-phase interval. -/
theorem short_far_slots : ∀ (d e : Direction) (a : Bool) (l : Fin (ShortCorners.count (cornerKindFor d e))),
    RectOrientation.Perpendicular d e →
    (farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).2=0 →
      (farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).1≤(a.toNat : ℤ)-2 := by
  decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting

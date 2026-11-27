/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortWallData

/-! Shared real anchors restrict every actual short-turn overlap to the checked constant-size line collars. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

private theorem near_coefficients : ∀ (d e : Direction) (flip : Bool),RectOrientation.Perpendicular d e →
    ((lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector (1,0))).1=-1 ∧
    ((lineOrientation d flip).inverseVector ((RectOrientation.choose d e).vector (0,1))).1=0 := by decide +kernel

private theorem far_coefficients : ∀ d e : Direction,RectOrientation.Perpendicular d e →
    ((lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector (1,0))).1=0 ∧
    ((lineOrientation e false).inverseVector ((RectOrientation.choose d e).vector (0,1))).1=1 := by decide +kernel

theorem nearRelative_x {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip : Bool) (p : ℤ×ℤ) :
    (nearRelative d e flip p).1=(ShortCorners.sourceX (cornerKindFor d e) : ℤ)-p.1 := by
  dsimp only [nearRelative]
  rw [RectOrientation.composition_x,(near_coefficients d e flip hd).1,(near_coefficients d e flip hd).2]
  omega

theorem farRelative_x {d e : Direction} (hd : RectOrientation.Perpendicular d e) (p : ℤ×ℤ) :
    (farRelative d e p).1=p.2-(ShortCorners.lastY (cornerKindFor d e)+2 : ℕ) := by
  dsimp only [farRelative]
  rw [RectOrientation.composition_x,(far_coefficients d e hd).1,(far_coefficients d e hd).2]
  omega

private theorem near_margin : ∀ k : ShortCorners.Kind,(ShortCorners.width k : ℤ)≤ShortCorners.sourceX k+5 := by decide +kernel
private theorem far_margin : ∀ k : ShortCorners.Kind,(ShortCorners.height k : ℤ)≤ShortCorners.lastY k+5 := by decide +kernel

/-- Any real common incoming pixel lies in the complete last seven columns of its arbitrary-length line. -/
theorem near_overlap_columns {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip : Bool)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (x span : ℕ)
    (hx : (x : ℤ)-(span+2 : ℕ)=(nearRelative d e flip (q.1.val,q.2.val)).1) : span≤x+2 := by
  rw [nearRelative_x hd] at hx
  have hq := q.1.isLt
  have hm := near_margin (cornerKindFor d e)
  omega

/-- Any real common outgoing pixel lies in the complete first five columns of its arbitrary-length line. -/
theorem far_overlap_columns {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (q : Cell (ShortCorners.width (cornerKindFor d e)) (ShortCorners.height (cornerKindFor d e)))
    (x : ℕ)
    (hx : (x : ℤ)-2=(farRelative d e (q.1.val,q.2.val)).1) : x<5 := by
  rw [farRelative_x hd] at hx
  have hq := q.2.isLt
  have hm := far_margin (cornerKindFor d e)
  omega

end PushPuzzle.PushFS.Reduction.GateTileRouting

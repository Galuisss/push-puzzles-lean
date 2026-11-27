/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortSlots
public import PushFS.RectPlacement

/-! Checked complete constant-size wall comparisons for every actual short-turn/long-line orientation. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

def ShortInside (k : ShortCorners.Kind) (p : ℤ×ℤ) : Prop :=
  0≤p.1 ∧ p.1<ShortCorners.width k ∧ 0≤p.2 ∧ p.2<ShortCorners.height k

instance (k : ShortCorners.Kind) (p : ℤ×ℤ) : Decidable (ShortInside k p) := by unfold ShortInside; infer_instance

def shortWall (k : ShortCorners.Kind) (p : ℤ×ℤ) : Bool :=
  if h : ShortInside k p then (ShortCorners.template k).wall
    (⟨p.1.toNat,by have := h.1; have := h.2.1; omega⟩,
     ⟨p.2.toNat,by have := h.2.2.1; have := h.2.2.2; omega⟩)
  else false

theorem shortWall_cell (k : ShortCorners.Kind) (p : Cell (ShortCorners.width k) (ShortCorners.height k)) :
    shortWall k (p.1.val,p.2.val)=(ShortCorners.template k).wall p := by
  have hp : ShortInside k (p.1.val,p.2.val) := by
    have hx := p.1.isLt
    have hy := p.2.isLt
    dsimp [ShortInside]
    omega
  rw [shortWall,dite_eq_left hp]
  congr 1

def nearSample (d e : Direction) (flip : Bool) (i : Fin 7) (y : Fin 21) : ℤ×ℤ :=
  let v := (RectOrientation.choose d e).inverseVector ((lineOrientation d flip).vector ((i.val : ℤ)-4,(y.val : ℤ)-10))
  ((ShortCorners.sourceX (cornerKindFor d e) : ℤ)+v.1,10+v.2)

def farSample (d e : Direction) (i : Fin 5) (y : Fin 21) : ℤ×ℤ :=
  let v := (RectOrientation.choose d e).inverseVector ((lineOrientation e false).vector ((i.val : ℤ)-2,(y.val : ℤ)-10))
  (10+v.1,(ShortCorners.lastY (cornerKindFor d e)+2 : ℕ)+v.2)

def farGuard (flip : Bool) (y : ℕ) : Bool := decide (if flip then y=8 ∨ y=9 else y=11 ∨ y=12)
def nearGuard (y : ℕ) : Bool := decide (y=11 ∨ y=12)

set_option maxRecDepth 65536
set_option maxHeartbeats 0

/-- All seven columns of every real incoming overlap agree with the actual chain or chain-plus-flip far guard. -/
theorem short_near_wall_checked : ∀ (d e : Direction) (flip : Bool) (i : Fin 7) (y : Fin 21),
    RectOrientation.Perpendicular d e → ShortInside (cornerKindFor d e) (nearSample d e flip i y) →
      shortWall (cornerKindFor d e) (nearSample d e flip i y)=farGuard flip y.val := by decide +kernel

/-- All five columns of every real outgoing overlap agree with the actual ordinary-chain near guard. -/
theorem short_far_wall_checked : ∀ (d e : Direction) (i : Fin 5) (y : Fin 21),
    RectOrientation.Perpendicular d e → ShortInside (cornerKindFor d e) (farSample d e i y) →
      shortWall (cornerKindFor d e) (farSample d e i y)=nearGuard y.val := by decide +kernel

end PushPuzzle.PushFS.Reduction.GateTileRouting

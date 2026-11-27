/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortWallGeometry
public import PushFS.Reduction.AnnulusShortOwners
public import PushFS.Gadgets.Wires.Catalog.EndpointBounds

/-! Exact phase-selected foreign short-turn boxes in the complete long-line endpoint collars. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 0

private theorem near_mask_checked : ∀ (d e : Direction) (flip a : Bool)
    (l : Fin (ShortCorners.count (cornerKindFor d e))),
    RectOrientation.Perpendicular d e →
    (nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).1<3 →
    -10≤(nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).2 →
    (nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).2<11 →
    (nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).2=0 ∧
      ((nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).1=a.toNat ∨
        a=false ∧(nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) a l)).1=2) := by
  decide +kernel

private theorem far_mask_checked : ∀ (d e : Direction) (a : Bool)
    (l : Fin (ShortCorners.count (cornerKindFor d e))),
    RectOrientation.Perpendicular d e →
    -2≤(farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).1 →
    -10≤(farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).2 →
    (farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).2<11 →
    (farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).2=0 ∧
      (farRelative d e (shortSlotCoordinates (cornerKindFor d e) a l)).1=(a.toNat : ℤ)-2 := by
  decide +kernel

/-- A complete incoming line sees exactly the first short-turn slot and, in phase zero, the next slot. -/
theorem short_near_line_slots {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip phase : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (hp : (lineOrientation d flip).coordinates _ _ dx dy p=
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l))
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    p.2.val=10 ∧(p.1.val=n+(if flip then 20 else 0)+2+phase.toNat ∨
      phase=false ∧p.1.val=n+(if flip then 20 else 0)+4) := by
  have hr:=(lineOrientation d flip).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    p (lineFarAnchor flip n hn a b) ((ShortCorners.template (cornerKindFor d e)).position phase l)
    (ShortCorners.nearAnchor (cornerKindFor d e)) hp ha
  change nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) phase l)=
    ((p.1.val : ℤ)-(n+(if flip then 20 else 0)+2 : ℕ),(p.2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  have hpx:=p.1.isLt
  have hpy:=p.2.isLt
  have hdims:=line_dimensions flip n hn a b
  have hpx' : p.1.val<n+(if flip then 25 else 5) := by omega
  have hpy' : p.2.val<21 := by omega
  have hm:=near_mask_checked d e flip phase l hd (by dsimp only at hx; cases flip <;> simp_all <;> omega)
    (by dsimp only at hy; omega) (by dsimp only at hy; omega)
  dsimp only at hx hy
  rcases hm with ⟨hmy,hmx|⟨hphase,hmx⟩⟩
  · exact ⟨by omega,Or.inl (by omega)⟩
  · exact ⟨by omega,Or.inr ⟨hphase,by omega⟩⟩

/-- A complete outgoing line sees precisely the last short-turn box at its true phase-selected near collar. -/
private theorem short_far_line_slots {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (phase : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase false n hn a b).width (lineBase false n hn a b).height)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (hp : (lineOrientation e false).coordinates _ _ dx dy p=
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l))
    (ha : (lineOrientation e false).coordinates _ _ dx dy (lineNearAnchor false n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    p.2.val=10 ∧p.1.val=phase.toNat := by
  have hr:=(lineOrientation e false).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    p (lineNearAnchor false n hn a b) ((ShortCorners.template (cornerKindFor d e)).position phase l)
    (ShortCorners.farAnchor (cornerKindFor d e)) hp ha
  change farRelative d e (shortSlotCoordinates (cornerKindFor d e) phase l)=
    ((p.1.val : ℤ)-2,(p.2.val : ℤ)-10) at hr
  have hx:=congrArg Prod.fst hr
  have hy:=congrArg Prod.snd hr
  have hpy:=p.2.isLt
  have hdims:=line_dimensions false n hn a b
  have hpy' : p.2.val<21 := by omega
  have hm:=far_mask_checked d e phase l hd (by dsimp only at hx; omega)
    (by dsimp only at hy; omega) (by dsimp only at hy; omega)
  dsimp only at hx hy
  exact ⟨by omega,by omega⟩

theorem short_far_line_slots_general {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (hf : flip=false) (phase : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (hp : (lineOrientation e flip).coordinates _ _ dx dy p=
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l))
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    p.2.val=10 ∧p.1.val=phase.toNat := by
  cases flip
  · exact short_far_line_slots hd phase n hn a b dx dy ex ey p l hp ha
  · cases hf

end PushPuzzle.PushFS.Reduction.GateTileRouting

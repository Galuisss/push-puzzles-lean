/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortSlots
public import PushFS.RectPlacement

/-! Real shared anchors separate the complete canonical long-line intervals from every actual protected-turn identity. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets.Wires

def lineNearAnchor (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  (⟨2,by rw [(line_dimensions flip n hn a b).1]; cases flip <;> simp⟩,
   ⟨10,by rw [(line_dimensions flip n hn a b).2]; decide⟩)

def lineFarAnchor (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  (⟨n+(if flip then 20 else 0)+2,by rw [(line_dimensions flip n hn a b).1]; cases flip <;> simp⟩,
   ⟨10,by rw [(line_dimensions flip n hn a b).2]; decide⟩)

/-- Every complete real incoming-line source or target interval is disjoint from the actual same-phase short turn. -/
theorem short_near_disjoint {d e : Direction} (hd : RectOrientation.Perpendicular d e) (flip phase : Bool)
    (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hx : p.1.val≤n+(if flip then 20 else 0)+phase.toNat) (hy : p.2.val=10)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    (lineOrientation d flip).coordinates _ _ dx dy p≠
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l) := by
  intro hp
  have hh := (lineOrientation d flip).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    p (lineFarAnchor flip n hn a b) ((ShortCorners.template (cornerKindFor d e)).position phase l)
    (ShortCorners.nearAnchor (cornerKindFor d e)) hp ha
  change nearRelative d e flip (shortSlotCoordinates (cornerKindFor d e) phase l)=
    ((p.1.val : ℤ)-(n+(if flip then 20 else 0)+2 : ℕ),(p.2.val : ℤ)-10) at hh
  have hhX := congrArg Prod.fst hh
  have hhY := congrArg Prod.snd hh
  have hslot := short_near_slots d e flip phase l hd (by dsimp only at hhY; omega)
  dsimp only at hhX
  omega

/-- Every complete real outgoing-line source or target interval is disjoint from the actual same-phase short turn. -/
private theorem short_far_disjoint {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (phase : Bool)
    (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase false n hn a b).width (lineBase false n hn a b).height)
    (hx : 2+phase.toNat≤p.1.val) (hy : p.2.val=10)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (ha : (lineOrientation e false).coordinates _ _ dx dy (lineNearAnchor false n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    (lineOrientation e false).coordinates _ _ dx dy p≠
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l) := by
  intro hp
  have hh := (lineOrientation e false).placed_inverse_relative (RectOrientation.choose d e) dx dy ex ey
    p (lineNearAnchor false n hn a b) ((ShortCorners.template (cornerKindFor d e)).position phase l)
    (ShortCorners.farAnchor (cornerKindFor d e)) hp ha
  change farRelative d e (shortSlotCoordinates (cornerKindFor d e) phase l)=
    ((p.1.val : ℤ)-2,(p.2.val : ℤ)-10) at hh
  have hhX := congrArg Prod.fst hh
  have hhY := congrArg Prod.snd hh
  have hslot := short_far_slots d e phase l hd (by dsimp only at hhY; omega)
  dsimp only at hhX
  omega

theorem short_far_disjoint_general {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (hf : flip=false) (phase : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (p : Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height)
    (hx : 2+phase.toNat≤p.1.val) (hy : p.2.val=10)
    (l : Fin (ShortCorners.count (cornerKindFor d e)))
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    (lineOrientation e flip).coordinates _ _ dx dy p≠
      (RectOrientation.choose d e).coordinates _ _ ex ey ((ShortCorners.template (cornerKindFor d e)).position phase l) := by
  cases flip
  · exact short_far_disjoint hd phase n hn a b dx dy ex ey p hx hy l ha
  · cases hf

end PushPuzzle.PushFS.Reduction.GateTileRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.AnnulusShortWallGeometry
public import PushFS.Reduction.AnnulusSeamAnchors
public import PushFS.Reduction.AnnulusFrontierGeometry
public import PushFS.Gadgets.Wires.ShortCorners.SeamWalking

/-! Real shared seam anchors identify complete long-line corners with protected-turn walking portals. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000

def nativeLineCorner : (flip : Bool)→(n : ℕ)→(hn : 2301≤n)→(a b : Bool)→(i : Fin 4)→
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height
  | false,n,_,_,_,i=>Chain.corner n i
  | true,n,_,_,_,i=>FlippedChain.corner n i

def nearPortalRelative (d e : Direction) (flip : Bool) : ℤ×ℤ :=
  let p:=ShortCorners.nearPortal (cornerKindFor d e)
  nearRelative d e flip (p.1.val,p.2.val)

def farPortalRelative (d e : Direction) : ℤ×ℤ :=
  let p:=ShortCorners.farPortal (cornerKindFor d e)
  farRelative d e (p.1.val,p.2.val)

def nearSeamCorner (d e : Direction) (flip : Bool) : Fin 4 :=
  if (nearPortalRelative d e flip).2= -9 then 1 else 3

def farSeamCorner (d e : Direction) : Fin 4 :=
  if (farPortalRelative d e).2= -9 then 0 else 2

private theorem near_relative_checked : ∀(d e : Direction) (flip : Bool),RectOrientation.Perpendicular d e →
    nearPortalRelative d e flip=(1,if nearSeamCorner d e flip=1 then -9 else 9) := by decide +kernel

private theorem far_relative_checked : ∀d e : Direction,RectOrientation.Perpendicular d e →
    farPortalRelative d e=(-1,if farSeamCorner d e=0 then -9 else 9) := by decide +kernel

private theorem near_corner_values (d e : Direction) (f : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    (nativeLineCorner f n hn a b (nearSeamCorner d e f)).1.val=n+(if f then 20 else 0)+3 ∧
    (nativeLineCorner f n hn a b (nearSeamCorner d e f)).2.val=if nearSeamCorner d e f=1 then 1 else 19 := by
  have hi : nearSeamCorner d e f=1 ∨nearSeamCorner d e f=3 := by
    unfold nearSeamCorner
    split_ifs <;> simp
  rcases hi with hi|hi <;> rw [hi] <;> cases f <;> exact ⟨rfl,rfl⟩

private theorem far_corner_values (d e : Direction) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    (nativeLineCorner false n hn a b (farSeamCorner d e)).1.val=1 ∧
    (nativeLineCorner false n hn a b (farSeamCorner d e)).2.val=if farSeamCorner d e=0 then 1 else 19 := by
  have hi : farSeamCorner d e=0 ∨farSeamCorner d e=2 := by
    unfold farSeamCorner
    split_ifs <;> simp
  rcases hi with hi|hi <;> rw [hi] <;> exact ⟨rfl,rfl⟩

private theorem placed_eq_of_inverse_relative {w h v z : ℕ} (o f : RectOrientation) (dx dy ex ey : ℕ)
    (p a : Cell w h) (q b : Cell v z)
    (ha : o.coordinates w h dx dy a=f.coordinates v z ex ey b)
    (hr : o.inverseVector (f.vector ((q.1.val : ℤ)-b.1.val,(q.2.val : ℤ)-b.2.val))=
      ((p.1.val : ℤ)-a.1.val,(p.2.val : ℤ)-a.2.val)) :
    o.coordinates w h dx dy p=f.coordinates v z ex ey q := by
  have hv:=congrArg o.vector hr
  rw [o.vector_inverseVector] at hv
  have hd:=(o.cells_difference w h p a).trans (hv.symm.trans (f.cells_difference v z q b).symm)
  have hax:=congrArg Prod.fst ha
  have hay:=congrArg Prod.snd ha
  have hdx:=congrArg Prod.fst hd
  have hdy:=congrArg Prod.snd hd
  dsimp only [RectOrientation.coordinates] at hax hay ⊢
  apply Prod.ext <;> dsimp only at hdx hdy ⊢ <;> omega

/-- An actual incoming long-line corner is exactly the protected turn's incoming free-lane portal. -/
theorem near_seam_corner {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (ha : (lineOrientation d flip).coordinates _ _ dx dy (lineFarAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearAnchor (cornerKindFor d e))) :
    (lineOrientation d flip).coordinates _ _ dx dy (nativeLineCorner flip n hn a b (nearSeamCorner d e flip))=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.nearPortal (cornerKindFor d e)) := by
  apply placed_eq_of_inverse_relative _ _ dx dy ex ey _ _ _ _ ha
  have hh:=near_relative_checked d e flip hd
  have hc:=near_corner_values d e flip n hn a b
  change nearPortalRelative d e flip=(_,_)
  rw [hh]
  apply Prod.ext
  · dsimp only
    change (1 : ℤ)=(nativeLineCorner flip n hn a b (nearSeamCorner d e flip)).1.val-
      (n+(if flip then 20 else 0)+2 : ℕ)
    rw [hc.1]
    omega
  · dsimp only
    change (if nearSeamCorner d e flip=1 then (-9 : ℤ) else 9)=
      (nativeLineCorner flip n hn a b (nearSeamCorner d e flip)).2.val-10
    rw [hc.2]
    split_ifs <;> omega

/-- An actual outgoing long-line corner is exactly the protected turn's outgoing free-lane portal. -/
private theorem far_seam_corner {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (ha : (lineOrientation e false).coordinates _ _ dx dy (lineNearAnchor false n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    (lineOrientation e false).coordinates _ _ dx dy (nativeLineCorner false n hn a b (farSeamCorner d e))=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farPortal (cornerKindFor d e)) := by
  apply placed_eq_of_inverse_relative _ _ dx dy ex ey _ _ _ _ ha
  have hh:=far_relative_checked d e hd
  have hc:=far_corner_values d e n hn a b
  change farPortalRelative d e=(_,_)
  rw [hh]
  apply Prod.ext
  · dsimp only
    change (-1 : ℤ)=(nativeLineCorner false n hn a b (farSeamCorner d e)).1.val-2
    rw [hc.1]
    decide
  · dsimp only
    change (if farSeamCorner d e=0 then (-9 : ℤ) else 9)=
      (nativeLineCorner false n hn a b (farSeamCorner d e)).2.val-10
    rw [hc.2]
    split_ifs <;> omega

theorem far_seam_corner_any {d e : Direction} (hd : RectOrientation.Perpendicular d e)
    (flip : Bool) (hf : flip=false) (n : ℕ) (hn : 2301≤n) (a b : Bool) (dx dy ex ey : ℕ)
    (ha : (lineOrientation e flip).coordinates _ _ dx dy (lineNearAnchor flip n hn a b)=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farAnchor (cornerKindFor d e))) :
    (lineOrientation e flip).coordinates _ _ dx dy (nativeLineCorner flip n hn a b (farSeamCorner d e))=
      (RectOrientation.choose d e).coordinates _ _ ex ey (ShortCorners.farPortal (cornerKindFor d e)) := by
  subst flip
  exact far_seam_corner hd n hn a b dx dy ex ey ha

def frontierLinePortal (flip : Bool) (n : ℕ) (hn : 2301≤n) (a b : Bool) :
    Cell (lineBase flip n hn a b).width (lineBase flip n hn a b).height :=
  (⟨3,by rw [(line_dimensions flip n hn a b).1]; cases flip <;> omega⟩,
    ⟨1,by rw [(line_dimensions flip n hn a b).2]; decide⟩)

/-- The true buffered-lead far corner is two outer-lane steps beyond the first line's near corner. -/
theorem frontier_seam_corner {n m : ℕ} (hm : 2301≤m) (flip : Bool) (a b : Bool)
    (o : RectOrientation) (dx dy ex ey : ℕ)
    (ha : o.coordinates (n+5) 21 dx dy (frontierLeadAnchor n)=
      o.coordinates _ _ ex ey (lineNearAnchor flip m hm a b)) :
    o.coordinates (n+5) 21 dx dy (Chain.corner n 1)=
      o.coordinates _ _ ex ey (frontierLinePortal flip m hm a b) := by
  apply placed_eq_of_inverse_relative _ _ dx dy ex ey _ _ _ _ ha
  rw [o.inverseVector_vector]
  apply Prod.ext
  · change ((3 : ℤ)-2)=((n+3 : ℕ) : ℤ)-(n+2 : ℕ)
    omega
  · rfl

end PushPuzzle.PushFS.Reduction.GateTileRouting

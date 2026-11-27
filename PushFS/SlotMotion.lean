/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.StorageAtlas
public import PushFS.RectOrientation
public import PushFS.SlotRelabel

/-! Canonical moves larger than one cell remain strictly inside their complete physical glyph. -/

@[expose] public section
namespace PushPuzzle.PushFS


namespace Cell

def UnitClose {w h : ℕ} (p q : Cell w h) : Prop :=
  p.1.val≤q.1.val+1 ∧q.1.val≤p.1.val+1 ∧p.2.val≤q.2.val+1 ∧q.2.val≤p.2.val+1

def Deep {w h : ℕ} (p : Cell w h) : Prop :=
  7≤p.1.val ∧p.1.val+7<w ∧7≤p.2.val ∧p.2.val+7<h

instance {w h : ℕ} (p q : Cell w h) : Decidable (UnitClose p q) := by unfold UnitClose; infer_instance
instance {w h : ℕ} (p : Cell w h) : Decidable (Deep p) := by unfold Deep; infer_instance

end Cell

structure SlotMotion {I : Instance} {L : Type} [Fintype L] (M : SlotMatching I L) : Prop where
  bound : ∀l, Cell.UnitClose (M.source l) (M.target l) ∨Cell.Deep (M.source l) ∧Cell.Deep (M.target l)

namespace SlotMotion

variable {w h W H : ℕ} {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}

theorem translate_pair (dx dy : ℕ) (hx : dx+w≤W) (hy : dy+h≤H) (p q : Cell w h)
    (hp : Cell.UnitClose p q ∨Cell.Deep p ∧Cell.Deep q) :
    Cell.UnitClose ((GridEmbedding.translate dx dy hx hy).cells p) ((GridEmbedding.translate dx dy hx hy).cells q) ∨
      Cell.Deep ((GridEmbedding.translate dx dy hx hy).cells p) ∧Cell.Deep ((GridEmbedding.translate dx dy hx hy).cells q) := by
  rcases hp with hp|⟨hp,hq⟩
  · left
    dsimp only [Cell.UnitClose] at hp
    change dx+p.1.val≤dx+q.1.val+1 ∧dx+q.1.val≤dx+p.1.val+1 ∧dy+p.2.val≤dy+q.2.val+1 ∧dy+q.2.val≤dy+p.2.val+1
    omega
  · right
    dsimp only [Cell.Deep] at hp hq
    change (7≤dx+p.1.val ∧dx+p.1.val+7<W ∧7≤dy+p.2.val ∧dy+p.2.val+7<H) ∧
      (7≤dx+q.1.val ∧dx+q.1.val+7<W ∧7≤dy+q.2.val ∧dy+q.2.val+7<H)
    omega

theorem atlas {n : ℕ} {Label : Fin n→Type} [∀i,Fintype (Label i)]
    (A : Reduction.StorageAtlas n W H Label) (hs : ∀i, SlotMotion (A.matching i)) : SlotMotion A.slotMatching where
  bound l:=translate_pair (A.dx l.1) (A.dy l.1) (A.fitsX l.1) (A.fitsY l.1) _ _ ((hs l.1).bound l.2)

private theorem oriented (o : RectOrientation) (p q : Cell w h)
    (hp : Cell.UnitClose p q ∨Cell.Deep p ∧Cell.Deep q) :
    Cell.UnitClose ((o.axis w h).geometry.cells p) ((o.axis w h).geometry.cells q) ∨
      Cell.Deep ((o.axis w h).geometry.cells p) ∧Cell.Deep ((o.axis w h).geometry.cells q) := by
  have hpx:=congrArg Prod.fst (o.point_cells w h p)
  have hpy:=congrArg Prod.snd (o.point_cells w h p)
  have hqx:=congrArg Prod.fst (o.point_cells w h q)
  have hqy:=congrArg Prod.snd (o.point_cells w h q)
  dsimp only at hpx hpy hqx hqy
  have hpi:=p.1.isLt
  have hpj:=p.2.isLt
  have hqi:=q.1.isLt
  have hqj:=q.2.isLt
  rcases o with ⟨swap,flipX,flipY⟩
  cases swap <;> cases flipX <;> cases flipY <;> rcases hp with hp|⟨hp,hq⟩
  all_goals simp only [Cell.UnitClose,Cell.Deep,RectOrientation.point,RectOrientation.width,
    RectOrientation.height,Bool.false_eq_true,ite_true,ite_false] at *
  all_goals omega

theorem reorient (hM : SlotMotion M) (o : RectOrientation) :
    SlotMotion (M.reorient (o.axis I.width I.height).geometry) where
  bound l:=oriented o _ _ (hM.bound l)

theorem reflectX (hM : SlotMotion M) : SlotMotion (M.reorient (GridIsometry.reflectX I.width I.height)) :=
  hM.reorient ⟨false,true,false⟩

theorem reflectY (hM : SlotMotion M) : SlotMotion (M.reorient (GridIsometry.reflectY I.width I.height)) :=
  hM.reorient ⟨false,false,true⟩

theorem transpose (hM : SlotMotion M) : SlotMotion (M.reorient (GridIsometry.transpose I.width I.height)) :=
  hM.reorient ⟨true,false,false⟩

end SlotMotion
end PushPuzzle.PushFS

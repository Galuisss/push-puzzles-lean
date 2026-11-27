/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMesh

/-! Literal same-stock walks along both clear halves of every actual coarse-grid side. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

/-- Both edge parameters lie on the same side of the central port band. -/
@[expose] def SameMeshHalf (w a b : ℕ) : Prop :=
  (a+(w+1) < 25*spacing w ∧ b+(w+1) < 25*spacing w) ∨
    (25*spacing w+(w+1) < a ∧ 25*spacing w+(w+1) < b)

private theorem coordinates_axes {W H : ℕ} {p q : Cell W H} {a b : ℕ × ℕ}
    (hp : coordinates p = a) (hq : coordinates q = b) :
    p.1.val = a.1 ∧ p.2.val = a.2 ∧ q.1.val = b.1 ∧ q.2.val = b.2 :=
  ⟨congrArg Prod.fst hp,congrArg Prod.snd hp,congrArg Prod.fst hq,congrArg Prod.snd hq⟩

theorem vertical_mesh_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (gx gy a b : ℕ) (ha' : a ≤ tileStride w) (hb : b ≤ tileStride w) (hhalf : SameMeshHalf w a b)
    (p q : Cell (width w v) (height w v))
    (hp : coordinates p = (tileStride w*gx+padding w,tileStride w*gy+padding w+a))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+b)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase p) (PrimitiveProfile.state w hw v phase q) := by
  obtain ⟨hpx,hpy,hqx,hqy⟩ := coordinates_axes hp hq
  have he : p.1 = q.1 := Fin.ext (hpx.trans hqx.symm)
  change Reachable _ _ ⟨(p.1,p.2),_⟩ ⟨(q.1,q.2),_⟩
  rw [←he]
  apply walk_vertical (PrimitiveProfile.floor ha phase)
  intro y hy hy'
  let t := y.val-(tileStride w*gy+padding w)
  have ht : min a b ≤ t ∧ t ≤ max a b := by dsimp [t]; omega
  have hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t := by
    dsimp [SameMeshHalf] at hhalf
    omega
  apply vertical_mesh_free w hw v phase gx gy t (by omega) hout (p.1,y)
  apply Prod.ext
  · exact hpx
  · dsimp [coordinates,t]
    omega

theorem horizontal_mesh_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (gx gy a b : ℕ) (ha' : a ≤ tileStride w) (hb : b ≤ tileStride w) (hhalf : SameMeshHalf w a b)
    (p q : Cell (width w v) (height w v))
    (hp : coordinates p = (tileStride w*gx+padding w+a,tileStride w*gy+padding w))
    (hq : coordinates q = (tileStride w*gx+padding w+b,tileStride w*gy+padding w)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase p) (PrimitiveProfile.state w hw v phase q) := by
  obtain ⟨hpx,hpy,hqx,hqy⟩ := coordinates_axes hp hq
  have he : p.2 = q.2 := Fin.ext (hpy.trans hqy.symm)
  change Reachable _ _ ⟨(p.1,p.2),_⟩ ⟨(q.1,q.2),_⟩
  rw [←he]
  apply walk_horizontal (PrimitiveProfile.floor ha phase)
  intro x hx hx'
  let t := x.val-(tileStride w*gx+padding w)
  have ht : min a b ≤ t ∧ t ≤ max a b := by dsimp [t]; omega
  have hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t := by
    dsimp [SameMeshHalf] at hhalf
    omega
  apply horizontal_mesh_free w hw v phase gx gy t (by omega) hout (x,p.2)
  apply Prod.ext
  · dsimp [coordinates,t]
    omega
  · exact hpy

end PushPuzzle.PushS.FiniteSourceInventory

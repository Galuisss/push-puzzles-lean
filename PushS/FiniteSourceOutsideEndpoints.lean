/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceOutsideHulls
public import PushS.FiniteSourceNormalSparse

/-! A selected one-step normal slot pair reserves both endpoint cells against outside stock. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

private theorem same_owner_position_injective (ha : (inventory w hw v).Admissible)
    (phase : Fin (codes w v).length → Bool) (l r : (inventory w hw v).PhysicalLabel)
    (ho : l.1 = r.1) (he : position w hw v phase l = position w hw v phase r) : l = r := by
  unfold position at he
  rw [ho] at he
  split at he
  · exact ha.target_injective he
  · exact ha.source_injective he

private theorem same_owner_position_sparse (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l r : (inventory w hw v).PhysicalLabel)
    (ho : l.1 = r.1)
    (hc : SameComponent (inventory w hw v).board (position w hw v phase l) (position w hw v phase r))
    (d : Direction) : ¬Adjacent d (position w hw v phase l) (position w hw v phase r) := by
  rcases l with ⟨i,l⟩
  rcases r with ⟨j,r⟩
  dsimp only at ho
  subst j
  exact normal_owner_sparse w hw v hP hT i (phase i) l r hc d

private theorem endpoint_owner_eq (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel)
    (p : Cell (width w v) (height w v))
    (hp : p = (inventory w hw v).source l ∨ p = (inventory w hw v).target l)
    (r : (inventory w hw v).PhysicalLabel) (he : position w hw v phase r = p) : l.1 = r.1 := by
  by_contra ho
  have hh : Hull (coordinates ((inventory w hw v).source l)) (coordinates ((inventory w hw v).target l)) (coordinates p) := by
    rcases hp with hp | hp <;> rw [hp] <;> dsimp [Hull] <;> omega
  have hstock := position_hull phase r
  rw [he] at hstock
  exact normal_travel_hulls_disjoint w hw v hP hT l r ho (coordinates p) hh hstock

/-- A normal box at either endpoint of a one-step slot pair is that pair's own identity. -/
theorem endpoint_label_unique (ha : (inventory w hw v).Admissible)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (l : (inventory w hw v).PhysicalLabel)
    (d : Direction) (hs : Adjacent d ((inventory w hw v).source l) ((inventory w hw v).target l))
    (p : Cell (width w v) (height w v))
    (hp : p = (inventory w hw v).source l ∨ p = (inventory w hw v).target l)
    (r : (inventory w hw v).PhysicalLabel) (he : position w hw v phase r = p) : r = l := by
  have ho := endpoint_owner_eq hP hT phase l p hp r he
  have hcur : position w hw v phase l = (inventory w hw v).source l ∨
      position w hw v phase l = (inventory w hw v).target l := by
    unfold position
    split <;> simp
  rcases hcur with hcur | hcur <;> rcases hp with hp | hp
  · exact (same_owner_position_injective ha phase l r ho (hcur.trans (hp.symm.trans he.symm))).symm
  · have hcomp : SameComponent (inventory w hw v).board (position w hw v phase l) (position w hw v phase r) := by
      rw [hcur,he,hp]
      exact connected w hw v hP hT l
    exfalso
    apply same_owner_position_sparse hP hT phase l r ho hcomp d
    rw [hcur,he,hp]
    exact hs
  · have hcomp : SameComponent (inventory w hw v).board (position w hw v phase l) (position w hw v phase r) := by
      rw [hcur,he,hp]
      exact (connected w hw v hP hT l).symm
    exfalso
    apply same_owner_position_sparse hP hT phase l r ho hcomp d.opposite
    rw [hcur,he,hp]
    exact hs.reverse
  · exact (same_owner_position_injective ha phase l r ho (hcur.trans (hp.symm.trans he.symm))).symm

theorem endpoint_pair_avoids (ha : (inventory w hw v).Admissible)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (selected : Finset (inventory w hw v).PhysicalLabel)
    (l : (inventory w hw v).PhysicalLabel) (hl : l ∈ selected)
    (d : Direction) (hs : Adjacent d ((inventory w hw v).source l) ((inventory w hw v).target l))
    (p : Cell (width w v) (height w v))
    (hp : p = (inventory w hw v).source l ∨ p = (inventory w hw v).target l) :
    p ∉ outside w hw v phase selected := by
  intro hm
  obtain ⟨r,hr,he⟩ := Finset.mem_image.mp hm
  have hr_eq := endpoint_label_unique ha hP hT phase l d hs p hp r he
  exact (Finset.mem_sdiff.mp hr).2 (hr_eq.symm ▸ hl)

end PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile

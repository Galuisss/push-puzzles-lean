/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingInventory
public import PushS.FiniteRoutingJunctions

/-! Actual inventory ownership and normal actor clearance under primitive placement. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

namespace PrimitiveCode

theorem world_injective (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) : Function.Injective (c.world w hw) := by
  intro p q he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  apply Prod.ext <;> apply Fin.ext
  · exact Nat.add_left_cancel hx
  · exact Nat.add_left_cancel hy

private theorem actor_injective (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (goal : Bool) :
    Function.Injective (c.actor w hw goal) := by
  cases goal <;> intro l r he
  · exact (c.matching w hw).source.injective (c.world_injective w hw he)
  · exact (c.matching w hw).target.injective (c.world_injective w hw he)

theorem actor_ne_own_wall (w : ℕ) (hw : 2 ≤ w) (c : PrimitiveCode) (goal : Bool) (l : c.Labels w)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) : c.actor w hw goal l ≠ c.world w hw p := by
  intro he
  have hcell := c.world_injective w hw he
  cases goal
  · have hs : (c.matching w hw).source l ∈ (c.instanceOf w hw).initial.boxes := by
      rw [←(c.matching w hw).source_image]
      exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
    change (c.matching w hw).source l = p at hcell
    rw [hcell] at hs
    exact Finset.disjoint_left.mp (c.instanceOf w hw).initial_valid.2.1 hs hp
  · have hs : (c.matching w hw).target l ∈ (c.instanceOf w hw).board.goals := by
      rw [←(c.matching w hw).target_image]
      exact Finset.mem_map.mpr ⟨l,Finset.mem_univ _,rfl⟩
    change (c.matching w hw).target l = p at hcell
    rw [hcell] at hs
    exact Finset.disjoint_left.mp (c.instanceOf w hw).goals_floor hp hs

end PrimitiveCode

structure InventoryActorsClear {n W H : ℕ} {Label : Fin n → Type} [∀ i, Fintype (Label i)]
    (A : InventoryAssembly n W H Label) : Prop where
  source_injective : Function.Injective A.source
  target_injective : Function.Injective A.target
  source_floor : ∀ l, A.source l ∉ A.walls
  target_floor : ∀ l, A.target l ∉ A.walls

theorem inventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (codes : List PrimitiveCode)
    (hf : ∀ c ∈ codes, PatchFits w (c.patch w hw))
    (hboxes : ∀ (i j : Fin codes.length), i ≠ j → ∀ (goal : Bool)
      (l : (codes.get i).Labels w) (r : (codes.get j).Labels w),
      (codes.get i).actor w hw goal l ≠ (codes.get j).actor w hw goal r)
    (hwalls : ∀ (i j : Fin codes.length), i ≠ j → ∀ (goal : Bool)
      (l : (codes.get i).Labels w)
      (p : Cell ((codes.get j).instanceOf w hw).width ((codes.get j).instanceOf w hw).height),
      p ∈ ((codes.get j).instanceOf w hw).board.walls →
      (codes.get i).actor w hw goal l ≠ (codes.get j).world w hw p) :
    InventoryActorsClear (inventory w hw codes hf) := by
  have hinj : ∀ goal : Bool, Function.Injective (fun l : (inventory w hw codes hf).PhysicalLabel =>
      if goal then (inventory w hw codes hf).target l else (inventory w hw codes hf).source l) := by
    intro goal ⟨i,l⟩ ⟨j,r⟩ he
    have he' : (codes.get i).actor w hw goal l = (codes.get j).actor w hw goal r := by
      cases goal <;> exact congrArg coordinates he
    by_cases hij : i = j
    · subst j
      have hl := (codes.get i).actor_injective w hw goal he'
      exact congrArg (Sigma.mk i) hl
    · exact (hboxes i j hij goal l r he').elim
  have hfloor : ∀ (goal : Bool) (l : (inventory w hw codes hf).PhysicalLabel),
      (if goal then (inventory w hw codes hf).target l else (inventory w hw codes hf).source l) ∉
        (inventory w hw codes hf).walls := by
    intro goal ⟨i,l⟩ hm
    obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
    have he' : (codes.get i).actor w hw goal l = (codes.get j).world w hw p := by
      cases goal <;> exact (congrArg coordinates he).symm
    by_cases hij : i = j
    · subst j
      exact (codes.get i).actor_ne_own_wall w hw goal l p hp he'
    · exact hwalls i j hij goal l p hp he'
  exact ⟨hinj false,hinj true,hfloor false,hfloor true⟩

end PushPuzzle.PushS.FiniteRouting

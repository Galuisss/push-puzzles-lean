/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateClearance

/-! The actual full three-arm gate bitmaps have complete clear normal inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem gateCodes_eq_specs (w : ℕ) (g : GateTileState) :
    gateCodes w g = .core g :: (List.finRange 3).flatMap (fun role => (armSpec w g role).codes) := rfl

theorem gateCodes_pairwise (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    (gateCodes w g).Pairwise (ActorsApart w hw) := by
  rw [gateCodes_eq_specs,List.pairwise_cons]
  refine ⟨?_,?_⟩
  · intro c hc
    obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact core_arm_actor_apart w hw g role c hc
  · apply List.pairwise_flatMap.mpr
    refine ⟨fun role _ => (armSpec w g role).codes_pairwise w hw (armSpec_geometry w g role),?_⟩
    apply List.Pairwise.imp _ (List.nodup_iff_pairwise_ne.mp (List.nodup_finRange 3))
    intro i j hij c hc d hd
    exact different_arms_actor_apart w hw g i j hij c d hc hd

theorem gateCodes_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (c : PrimitiveCode) (hc : c ∈ gateCodes w g) (d : PrimitiveCode) (hd : d ∈ gateCodes w g) :
    ActorWallsClear w hw c d := by
  rw [gateCodes_eq_specs] at hc hd
  rcases List.mem_cons.mp hc with rfl | hc <;> rcases List.mem_cons.mp hd with rfl | hd
  · exact PrimitiveCode.actor_ne_own_wall w hw (.core g)
  · obtain ⟨role,_,hd⟩ := List.mem_flatMap.mp hd
    exact core_arm_wall_clear w hw g role d hd
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    exact arm_core_wall_clear w hw g role c hc
  · obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨j,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases hij : i = j
    · subst j
      exact (armSpec w g i).codes_wall_clear w hw (armSpec_geometry w g i) c hc d hd
    · exact different_arms_wall_clear w hw g i j hij c d hc hd

/-- Every actual parameterized gate tile has unique complete normal boxes and clear union floor. -/
theorem gateInventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    InventoryActorsClear (gateInventory w hw g) := by
  apply inventory_actorsClear
  · intro i j hij goal l r
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hlt
    · have h := List.pairwise_iff_getElem.mp (gateCodes_pairwise w hw g) i.val j.val i.isLt j.isLt hlt
      exact h goal l r
    · have h := List.pairwise_iff_getElem.mp (gateCodes_pairwise w hw g) j.val i.val j.isLt i.isLt hlt
      exact Ne.symm (h goal r l)
  · intro i j _ goal l p hp
    exact gateCodes_wall_clear w hw g _ (List.get_mem _ _) _ (List.get_mem _ _) goal l p hp

end PushPuzzle.PushS.FiniteRouting

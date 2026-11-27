/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceFloor

/-! Test the emitted wall union through the actual coordinates of its primitive owners. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height InventoryAssembly.walls

theorem floor_of_wall_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (q : Cell (width w v) (height w v))
    (h : ∀ (i : Fin (codes w v).length)
      (p : Cell ((inventory w hw v).piece i).width ((inventory w hw v).piece i).height),
      p ∈ ((inventory w hw v).piece i).board.walls →
      coordinates q ≠ macroShift w ((codes w v).get i).1 (((codes w v).get i).2.world w hw p)) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  unfold InventoryAssembly.walls at hm
  obtain ⟨i,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  exact h i p hp ((congrArg coordinates he).symm.trans (placed_wall_coordinates w hw v i p))

end PushPuzzle.PushS.FiniteSourceInventory

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurns
public import PushFS.StaticLine
public import PushFS.StaticTracks

/-! Physical slot matchings for the two owned boxes of every placed concave turn. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting.Turn

open PushFS FiniteTools FiniteGeometry

attribute [local irreducible] FiniteTools.side

private def floorLine (w : ℕ) (role : Fin 2) (i : Fin 4) :
    Cell (FiniteTools.side w) (FiniteTools.side w) :=
  if role = 0 then
    (⟨radius w-3+i.val,by unfold FiniteTools.side radius; have hi := i.isLt; omega⟩,
     ⟨radius w,by unfold FiniteTools.side; omega⟩)
  else
    (⟨radius w,by unfold FiniteTools.side; omega⟩,
     ⟨radius w+i.val,by unfold FiniteTools.side radius; have hi := i.isLt; omega⟩)

private theorem floorLine_floor (w : ℕ) (role : Fin 2) (i : Fin 4) : floorLine w role i ∉ turnWalls w := by
  apply turnActive_floor w
  rw [turnActive, Rectangle.mem_cells]
  have hi := i.isLt
  fin_cases role <;> dsimp [floorLine, radius] <;> omega

private theorem floorLine_adjacent (w : ℕ) (role : Fin 2) (i : Fin 3) :
    Adjacent (if role = 0 then .east else .south)
      (floorLine w role i.castSucc) (floorLine w role i.succ) := by
  fin_cases role <;> dsimp [floorLine, Adjacent] <;> constructor <;> rfl

private def slotIndex (q : Bool) : Fin 4 := ⟨q.toNat+1,by have hq := Bool.toNat_le q; omega⟩

private theorem floorLine_slot (w : ℕ) (q : Bool) (role : Fin 2) :
    floorLine w role (slotIndex q) = cell w q role := by
  apply Prod.ext <;> apply Fin.ext
  all_goals fin_cases role <;> cases q <;>
    dsimp [floorLine, slotIndex, cell, label, turnMixedCell, turnMixedPoint, radius] <;> omega

theorem cell_connected (w : ℕ) (a b : Bool)
    (goals : Finset (Cell (FiniteTools.side w) (FiniteTools.side w))) (role : Fin 2) :
    SameComponent (⟨turnWalls w,goals⟩ : Board (FiniteTools.side w) (FiniteTools.side w))
      (cell w a role) (cell w b role) := by
  have hh := sameComponent_line (n := 1) (d := if role = 0 then .east else .south)
    (B := (⟨turnWalls w,goals⟩ : Board (FiniteTools.side w) (FiniteTools.side w)))
    (floorLine w role) (floorLine_floor w role) (floorLine_adjacent w role)
    (slotIndex a) (slotIndex b)
    (by dsimp [slotIndex]; have hq := Bool.toNat_le a; omega)
    (by dsimp [slotIndex]; have hq := Bool.toNat_le b; omega)
  simpa only [floorLine_slot] using hh

def matching (w : ℕ) (initial target : Bool) : SlotMatching (puzzle w initial target) (Fin 2) where
  source := ⟨cell w initial,cell_injective w initial⟩
  target := ⟨cell w target,cell_injective w target⟩
  source_image := Finset.map_eq_image _ _
  target_image := Finset.map_eq_image _ _
  connected := cell_connected w initial target _

end PushPuzzle.PushS.FiniteRouting.Turn

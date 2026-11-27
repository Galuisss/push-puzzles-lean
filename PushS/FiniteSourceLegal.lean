/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceOwnership
public import PushS.FiniteSourcePlayer
public import PushS.FiniteSourceWalls

/-! The actual whole-board source emitter is a complete legal finite storage instance. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction

attribute [local irreducible] codes width height

/-- All actual primitive walls, owned boxes, targets and the exterior player form one legal board. -/
theorem admissible (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : (inventory w hw v).Admissible := by
  have hc := inventory_actorsClear w hw v hP hT
  exact ⟨hc.source_injective,hc.target_injective,hc.source_floor,hc.target_floor,
    player_floor w hw v,player_empty w hw v⟩

def checkedPuzzle (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : PushFS.Instance :=
  puzzle w hw v (admissible w hw v hP hT)

theorem checkedPuzzle_data (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Encoding.data (checkedPuzzle w hw v hP hT) = (table w hw).data v :=
  puzzle_data w hw v _

end PushPuzzle.PushS.FiniteSourceInventory

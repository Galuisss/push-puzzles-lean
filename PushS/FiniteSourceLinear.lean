/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceAxisMosaic
public import PushS.FiniteSourceLegal
public import PushFS.RailTags

/-! C2 for the complete emitted finite-force source inventory. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

theorem initial_component_linear (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (width w v) (height w v)) (hp : p ∈ (inventory w hw v).initial.boxes) :
    ComponentLinear (component (inventory w hw v).board p) :=
  (axisClassifier w hw v hP hT).component_linear p (axis_initial_active w hw v hP hT p hp)

theorem checkedPuzzle_linear (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (checkedPuzzle w hw v hP hT).width (checkedPuzzle w hw v hP hT).height)
    (hp : p ∈ (checkedPuzzle w hw v hP hT).initial.boxes) :
    ComponentLinear (component (checkedPuzzle w hw v hP hT).board p) :=
  initial_component_linear w hw v hP hT p hp

end PushPuzzle.PushS.FiniteSourceInventory

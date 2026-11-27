/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCertificate

/-! Same-owner normal stocks stay sparse along every actual displacement component. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

theorem normal_owner_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : Fin (codes w v).length) (goal : Bool) (l r : Label w v i)
    (he : SameComponent (inventory w hw v).board
      (if goal then (inventory w hw v).target ⟨i,l⟩ else (inventory w hw v).source ⟨i,l⟩)
      (if goal then (inventory w hw v).target ⟨i,r⟩ else (inventory w hw v).source ⟨i,r⟩)) (d : Direction) :
    ¬Adjacent d
      (if goal then (inventory w hw v).target ⟨i,l⟩ else (inventory w hw v).source ⟨i,l⟩)
      (if goal then (inventory w hw v).target ⟨i,r⟩ else (inventory w hw v).source ⟨i,r⟩) := by
  exact primitive_normal_sparse w hw v hP hT i ((codes w v).get i).2 rfl goal l r
    ((axisClassifier w hw v hP hT).name_eq_of_sameComponent he) d

end PushPuzzle.PushS.FiniteSourceInventory

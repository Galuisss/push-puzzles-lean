/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTravelHulls
public import PushS.FiniteSourcePrimitiveOrder
public import PushS.FiniteSourceLinear
public import PushS.FiniteSourceConnectivity
public import PushFS.LabelOrder

/-! The actual complete finite-force source slot matching preserves physical order in every SCC. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

private theorem foreign_slot_order (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i j : (inventory w hw v).PhysicalLabel) (hne : i.1 ≠ j.1)
    (hc : component (inventory w hw v).board ((inventory w hw v).source i) =
      component (inventory w hw v).board ((inventory w hw v).source j)) :
    (((inventory w hw v).source i).1.val < ((inventory w hw v).source j).1.val →
      ((inventory w hw v).target i).1.val < ((inventory w hw v).target j).1.val) ∧
    (((inventory w hw v).source i).2.val < ((inventory w hw v).source j).2.val →
      ((inventory w hw v).target i).2.val < ((inventory w hw v).target j).2.val) := by
  let A := inventory w hw v
  change ((A.source i).1.val < (A.source j).1.val → (A.target i).1.val < (A.target j).1.val) ∧
    ((A.source i).2.val < (A.source j).2.val → (A.target i).2.val < (A.target j).2.val)
  change component A.board (A.source i) = component A.board (A.source j) at hc
  have hp : A.source i ∈ A.initial.boxes := Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  have hlin := initial_component_linear w hw v hP hT (A.source i) hp
  have hi : component A.board (A.target i) = component A.board (A.source i) :=
    (component_eq_iff.mpr (connected w hw v hP hT i)).symm
  have hj : component A.board (A.target j) = component A.board (A.source i) :=
    (component_eq_iff.mpr (connected w hw v hP hT j)).symm.trans hc.symm
  constructor
  · intro ho
    by_contra ht
    rcases hlin with hlin | hlin
    · have he := congrArg Fin.val (hlin (A.source i) (A.source j) rfl hc.symm)
      omega
    · have he := congrArg Fin.val (hlin (A.source i) (A.source j) rfl hc.symm)
      have he' := congrArg Fin.val (hlin (A.source i) (A.target i) rfl hi)
      have he'' := congrArg Fin.val (hlin (A.source i) (A.target j) rfl hj)
      let p := (max (min (A.source i).1.val (A.target i).1.val) (min (A.source j).1.val (A.target j).1.val),(A.source i).2.val)
      have hip : Hull (coordinates (A.source i)) (coordinates (A.target i)) p := by
        dsimp [Hull,coordinates,p]
        omega
      have hjp : Hull (coordinates (A.source j)) (coordinates (A.target j)) p := by
        dsimp [Hull,coordinates,p]
        omega
      exact normal_travel_hulls_disjoint w hw v hP hT i j hne p hip hjp
  · intro ho
    by_contra ht
    rcases hlin with hlin | hlin
    · have he := congrArg Fin.val (hlin (A.source i) (A.source j) rfl hc.symm)
      have he' := congrArg Fin.val (hlin (A.source i) (A.target i) rfl hi)
      have he'' := congrArg Fin.val (hlin (A.source i) (A.target j) rfl hj)
      let p := ((A.source i).1.val,max (min (A.source i).2.val (A.target i).2.val) (min (A.source j).2.val (A.target j).2.val))
      have hip : Hull (coordinates (A.source i)) (coordinates (A.target i)) p := by
        dsimp [Hull,coordinates,p]
        omega
      have hjp : Hull (coordinates (A.source j)) (coordinates (A.target j)) p := by
        dsimp [Hull,coordinates,p]
        omega
      exact normal_travel_hulls_disjoint w hw v hP hT i j hne p hip hjp
    · have he := congrArg Fin.val (hlin (A.source i) (A.source j) rfl hc.symm)
      omega

private theorem same_primitive_slot_order (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i j : (inventory w hw v).PhysicalLabel) (he : i.1 = j.1)
    (hc : component (inventory w hw v).board ((inventory w hw v).source i) =
      component (inventory w hw v).board ((inventory w hw v).source j)) :
    (((inventory w hw v).source i).1.val < ((inventory w hw v).source j).1.val →
      ((inventory w hw v).target i).1.val < ((inventory w hw v).target j).1.val) ∧
    (((inventory w hw v).source i).2.val < ((inventory w hw v).source j).2.val →
      ((inventory w hw v).target i).2.val < ((inventory w hw v).target j).2.val) := by
  rcases i with ⟨i,l⟩
  rcases j with ⟨j,r⟩
  dsimp at he
  subst j
  exact primitive_slot_order w hw v hP hT i ((codes w v).get i).2 rfl l r hc

/-- Actual source/target labels keep both coordinate orders within their initial displacement SCC. -/
theorem ordered (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (slotMatching w hw v hP hT).Ordered := by
  have horder (i j : (inventory w hw v).PhysicalLabel)
      (hc : component (inventory w hw v).board ((inventory w hw v).source i) =
        component (inventory w hw v).board ((inventory w hw v).source j)) := by
    by_cases he : i.1 = j.1
    · exact same_primitive_slot_order w hw v hP hT i j he hc
    · exact foreign_slot_order w hw v hP hT i j he hc
  exact ⟨fun i j hc => (horder i j hc).1,fun i j hc => (horder i j hc).2⟩

end PushPuzzle.PushS.FiniteSourceInventory

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePrimitiveSparse
public import PushS.FiniteSourceLinear
public import PushS.FiniteSourceSpacing

/-! C1–C3 for the actual complete parameterized thick-wall source board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

theorem targets_axis_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (width w v) (height w v)) (hp : p ∈ (inventory w hw v).board.goals)
    (q : Cell (width w v) (height w v)) (hq : q ∈ (inventory w hw v).board.goals)
    (he : (axisClassifier w hw v hP hT).name p = (axisClassifier w hw v hP hT).name q) (d : Direction) :
    ¬Adjacent d p q := by
  unfold InventoryAssembly.board at hp hq
  obtain ⟨⟨i,l⟩,_,rfl⟩ := Finset.mem_image.mp hp
  obtain ⟨⟨j,r⟩,_,rfl⟩ := Finset.mem_image.mp hq
  by_cases hij : i = j
  · subst j
    exact primitive_normal_sparse w hw v hP hT i ((codes w v).get i).2 rfl true l r he d
  · exact normal_primitive_sparse w hw v hP hT i j hij true l r d

private theorem targets_separated (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p : Cell (width w v) (height w v)) (hp : p ∈ (inventory w hw v).board.goals)
    (q : Cell (width w v) (height w v)) (hq : q ∈ (inventory w hw v).board.goals)
    (he : component (inventory w hw v).board p = component (inventory w hw v).board q) (d : Direction) :
    ¬Adjacent d p q :=
  targets_axis_sparse w hw v hP hT p hp q hq
    ((axisClassifier w hw v hP hT).name_eq_of_sameComponent (component_eq_iff.mp he)) d

theorem certificate (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : Certificate (checkedPuzzle w hw v hP hT) :=
  ⟨componentBalanced w hw v hP hT,checkedPuzzle_linear w hw v hP hT,targets_separated w hw v hP hT⟩

/-- The actual complete board tracks, with literal initial activity and separated storage goals. -/
@[expose] noncomputable def axisTracks (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : AxisTracks (checkedPuzzle w hw v hP hT) where
  name := (axisClassifier w hw v hP hT).name
  supported := (axisClassifier w hw v hP hT).supported
  active := axis_initial_active w hw v hP hT
  displacement := (axisClassifier w hw v hP hT).displacement
  separated := targets_axis_sparse w hw v hP hT

end PushPuzzle.PushS.FiniteSourceInventory

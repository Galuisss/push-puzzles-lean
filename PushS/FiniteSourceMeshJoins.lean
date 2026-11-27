/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshTight
public import PushS.FiniteSourceMeshNodes
public import PushS.FiniteSourceNormalWalking

/-! Real one-cell same-stock joins connect the proved mesh half-edges to the literal port shoulders. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

private theorem step_both (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (p q : Cell (width w v) (height w v)) (d : Direction) (hadj : Adjacent d p q)
    (hp : Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) p)
    (hq : Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase p) (PrimitiveProfile.state w hw v phase q) ∧
      Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase p) :=
  ⟨normal_profile_step w hw v ha phase p q d hadj hp hq,
    normal_profile_step w hw v ha phase q p d.opposite hadj.reverse hq hp⟩

theorem vertical_low_shoulder_join (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w,tileStride w*y.val+padding w+(25*spacing w-(w+1)))) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshLow w))) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshLow w))) := by
  apply step_both w hw v ha phase _ q .south
  · apply adjacent_of_coordinates
    rw [hq]
    dsimp [verticalSide,meshNode,meshLow,coordinates,Travels]
    constructor
    · rfl
    · unfold spacing
      omega
  · apply vertical_mesh_free_tight w hw v phase x.val y.val (25*spacing w-(w+2))
      (by unfold tileStride spacing; omega) (by unfold spacing; omega) _ rfl
  · exact vertical_mesh_free_tight w hw v phase x.val y.val (25*spacing w-(w+1))
      (by unfold tileStride spacing; omega) (by unfold spacing; omega) q hq

theorem vertical_high_shoulder_join (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w,tileStride w*y.val+padding w+(25*spacing w+(w+1)))) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshHigh w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshHigh w))) (PrimitiveProfile.state w hw v phase q) := by
  apply step_both w hw v ha phase q _ .south
  · apply adjacent_of_coordinates
    rw [hq]
    dsimp [verticalSide,meshNode,meshHigh,coordinates,Travels]
    constructor
    · rfl
    · omega
  · exact vertical_mesh_free_tight w hw v phase x.val y.val (25*spacing w+(w+1))
      (by unfold tileStride spacing; omega) (by omega) q hq
  · apply vertical_mesh_free_tight w hw v phase x.val y.val (25*spacing w+(w+2))
      (by unfold tileStride spacing; omega) (by omega) _ rfl

theorem horizontal_low_shoulder_join (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w+(25*spacing w-(w+1)),tileStride w*y.val+padding w)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshLow w))) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshLow w))) := by
  apply step_both w hw v ha phase _ q .east
  · apply adjacent_of_coordinates
    rw [hq]
    dsimp [horizontalSide,meshNode,meshLow,coordinates,Travels]
    constructor
    · rfl
    · unfold spacing
      omega
  · apply horizontal_mesh_free_tight w hw v phase x.val y.val (25*spacing w-(w+2))
      (by unfold tileStride spacing; omega) (by unfold spacing; omega) _ rfl
  · exact horizontal_mesh_free_tight w hw v phase x.val y.val (25*spacing w-(w+1))
      (by unfold tileStride spacing; omega) (by unfold spacing; omega) q hq

theorem horizontal_high_shoulder_join (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w+(25*spacing w+(w+1)),tileStride w*y.val+padding w)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshHigh w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshHigh w))) (PrimitiveProfile.state w hw v phase q) := by
  apply step_both w hw v ha phase q _ .east
  · apply adjacent_of_coordinates
    rw [hq]
    dsimp [horizontalSide,meshNode,meshHigh,coordinates,Travels]
    constructor
    · rfl
    · omega
  · exact horizontal_mesh_free_tight w hw v phase x.val y.val (25*spacing w+(w+1))
      (by unfold tileStride spacing; omega) (by omega) q hq
  · apply horizontal_mesh_free_tight w hw v phase x.val y.val (25*spacing w+(w+2))
      (by unfold tileStride spacing; omega) (by omega) _ rfl

end PushPuzzle.PushS.FiniteSourceInventory

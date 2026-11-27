/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshOrigin

/-! Literal coarse-grid nodes and the four proved clear node-to-port-approach walks. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Raster.width Raster.height

/-- A padded vertex of the coarse source-grid walking mesh. -/
@[expose] def meshNode (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1+1)) : Cell (width w v) (height w v) :=
  (⟨tileStride w*x.val+padding w,by
      have h := Nat.mul_le_mul_left (tileStride w) (show x.val ≤ Raster.width v.1 by have h := x.isLt; omega)
      unfold width
      omega⟩,
   ⟨tileStride w*y.val+padding w,by
      have h := Nat.mul_le_mul_left (tileStride w) (show y.val ≤ Raster.height v.1 by have h := y.isLt; omega)
      unfold height
      omega⟩)

/-- A cell along a vertical coarse-grid mesh edge. -/
@[expose] def verticalSide (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (t : Fin (tileStride w+1)) :
    Cell (width w v) (height w v) :=
  ( (meshNode w v x y.castSucc).1,
    ⟨tileStride w*y.val+padding w+t.val,by
      have h := Nat.mul_le_mul_left (tileStride w) (show y.val+1 ≤ Raster.height v.1 by have h := y.isLt; omega)
      rw [Nat.mul_add,Nat.mul_one] at h
      have ht := t.isLt
      unfold height
      omega⟩)

/-- A cell along a horizontal coarse-grid mesh edge. -/
@[expose] def horizontalSide (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (t : Fin (tileStride w+1)) :
    Cell (width w v) (height w v) :=
  (⟨tileStride w*x.val+padding w+t.val,by
      have h := Nat.mul_le_mul_left (tileStride w) (show x.val+1 ≤ Raster.width v.1 by have h := x.isLt; omega)
      rw [Nat.mul_add,Nat.mul_one] at h
      have ht := t.isLt
      unfold width
      omega⟩,
    (meshNode w v x.castSucc y).2)

/-- The mesh point immediately below the lower port shoulder. -/
@[expose] def meshLow (w : ℕ) : Fin (tileStride w+1) :=
  ⟨25*spacing w-(w+2),by unfold tileStride; omega⟩

/-- The mesh point immediately above the upper port shoulder. -/
@[expose] def meshHigh (w : ℕ) : Fin (tileStride w+1) :=
  ⟨25*spacing w+(w+2),by unfold tileStride spacing; omega⟩

theorem verticalSide_zero (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) :
    verticalSide w v x y 0 = meshNode w v x y.castSucc := by rfl

theorem verticalSide_last (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) :
    verticalSide w v x y (Fin.last (tileStride w)) = meshNode w v x y.succ := by
  apply Prod.ext
  · rfl
  · apply Fin.ext
    dsimp [verticalSide,meshNode]
    simp only [Nat.mul_add,Nat.mul_one]
    omega

theorem horizontalSide_zero (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) :
    horizontalSide w v x y 0 = meshNode w v x.castSucc y := by rfl

theorem horizontalSide_last (w : ℕ) (v : CellPlan.Source)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) :
    horizontalSide w v x y (Fin.last (tileStride w)) = meshNode w v x.succ y := by
  apply Prod.ext
  · apply Fin.ext
    dsimp [horizontalSide,meshNode]
    simp only [Nat.mul_add,Nat.mul_one]
    omega
  · rfl

theorem vertical_side_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1))
    (a b : Fin (tileStride w+1)) (hhalf : SameMeshHalf w a.val b.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y a))
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y b)) :=
  vertical_mesh_walk w hw v ha phase x.val y.val a.val b.val (by have h := a.isLt; omega)
    (by have h := b.isLt; omega) hhalf _ _ rfl rfl

theorem horizontal_side_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1))
    (a b : Fin (tileStride w+1)) (hhalf : SameMeshHalf w a.val b.val) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y a))
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y b)) :=
  horizontal_mesh_walk w hw v ha phase x.val y.val a.val b.val (by have h := a.isLt; omega)
    (by have h := b.isLt; omega) hhalf _ _ rfl rfl

theorem meshLow_half (w : ℕ) : SameMeshHalf w 0 (meshLow w).val := by
  apply Or.inl
  dsimp [meshLow]
  unfold spacing
  omega

theorem meshHigh_half (w : ℕ) : SameMeshHalf w (meshHigh w).val (tileStride w) := by
  apply Or.inr
  dsimp [meshHigh]
  unfold tileStride spacing
  omega

end PushPuzzle.PushS.FiniteSourceInventory

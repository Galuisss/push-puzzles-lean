/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshCrossing
public import PushS.FiniteSourceMeshUnused

/-! Complete real coarse-grid connectivity follows by explicit row-then-column walks and normal flip detours. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Raster.width Raster.height

theorem SameMeshHalf.symm {w a b : ℕ} (h : SameMeshHalf w a b) : SameMeshHalf w b a := by
  rcases h with h | h
  · exact Or.inl ⟨h.2,h.1⟩
  · exact Or.inr ⟨h.2,h.1⟩

private theorem vertical_mesh_edge_of_mouths (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hm : ∀ s : LineSite w hw v, s.MouthsFree phase)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (meshNode w v x y.castSucc))
      (PrimitiveProfile.state w hw v phase (meshNode w v x y.succ)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (meshNode w v x y.succ))
      (PrimitiveProfile.state w hw v phase (meshNode w v x y.castSucc)) := by
  by_cases hu : CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .west
  · have hcross := vertical_used_mesh_crossing w hw v ha hP hT phase hm x y hu
    have hbefore := vertical_side_walk w hw v ha phase x y 0 (meshLow w) (meshLow_half w)
    have hbefore' := vertical_side_walk w hw v ha phase x y (meshLow w) 0 (meshLow_half w).symm
    have hafter := vertical_side_walk w hw v ha phase x y (meshHigh w) (Fin.last (tileStride w)) (meshHigh_half w)
    have hafter' := vertical_side_walk w hw v ha phase x y (Fin.last (tileStride w)) (meshHigh w) (meshHigh_half w).symm
    exact ⟨by simpa only [verticalSide_zero,verticalSide_last] using hbefore.trans (hcross.1.trans hafter),
      by simpa only [verticalSide_zero,verticalSide_last] using hafter'.trans (hcross.2.trans hbefore')⟩
  · exact ⟨by simpa only [verticalSide_zero,verticalSide_last] using
        vertical_unused_side_walk w hw v ha hP hT phase x y hu 0 (Fin.last (tileStride w)),
      by simpa only [verticalSide_zero,verticalSide_last] using
        vertical_unused_side_walk w hw v ha hP hT phase x y hu (Fin.last (tileStride w)) 0⟩

private theorem horizontal_mesh_edge_of_mouths (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hm : ∀ s : LineSite w hw v, s.MouthsFree phase)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (meshNode w v x.castSucc y))
      (PrimitiveProfile.state w hw v phase (meshNode w v x.succ y)) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (meshNode w v x.succ y))
      (PrimitiveProfile.state w hw v phase (meshNode w v x.castSucc y)) := by
  by_cases hu : CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .north
  · have hcross := horizontal_used_mesh_crossing w hw v ha hP hT phase hm x y hu
    have hbefore := horizontal_side_walk w hw v ha phase x y 0 (meshLow w) (meshLow_half w)
    have hbefore' := horizontal_side_walk w hw v ha phase x y (meshLow w) 0 (meshLow_half w).symm
    have hafter := horizontal_side_walk w hw v ha phase x y (meshHigh w) (Fin.last (tileStride w)) (meshHigh_half w)
    have hafter' := horizontal_side_walk w hw v ha phase x y (Fin.last (tileStride w)) (meshHigh w) (meshHigh_half w).symm
    exact ⟨by simpa only [horizontalSide_zero,horizontalSide_last] using hbefore.trans (hcross.1.trans hafter),
      by simpa only [horizontalSide_zero,horizontalSide_last] using hafter'.trans (hcross.2.trans hbefore')⟩
  · exact ⟨by simpa only [horizontalSide_zero,horizontalSide_last] using
        horizontal_unused_side_walk w hw v ha hP hT phase x y hu 0 (Fin.last (tileStride w)),
      by simpa only [horizontalSide_zero,horizontalSide_last] using
        horizontal_unused_side_walk w hw v ha hP hT phase x y hu (Fin.last (tileStride w)) 0⟩

theorem mesh_node_access_of_mouths (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hm : ∀ s : LineSite w hw v, s.MouthsFree phase)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1+1)) :
    NormalAnchorAccess w hw v phase (meshNode w v x y) := by
  have row (a : Fin (Raster.width v.1+1)) :
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (meshOrigin w v))
        (PrimitiveProfile.state w hw v phase (meshNode w v a 0)) ∧
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (meshNode w v a 0))
        (PrimitiveProfile.state w hw v phase (meshOrigin w v)) := by
    induction a using Fin.induction with
    | zero =>
      have he : meshNode w v 0 0 = meshOrigin w v := by
        apply Prod.ext <;> apply Fin.ext <;> simp [meshNode,meshOrigin]
      rw [he]
      exact ⟨.refl,.refl⟩
    | succ a ih =>
      have hstep := horizontal_mesh_edge_of_mouths w hw v ha hP hT phase hm a 0
      exact ⟨ih.1.trans hstep.1,hstep.2.trans ih.2⟩
  have col (a : Fin (Raster.width v.1+1)) (b : Fin (Raster.height v.1+1)) :
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (meshNode w v a 0))
        (PrimitiveProfile.state w hw v phase (meshNode w v a b)) ∧
      Reachable (inventory w hw v).board (some 1)
        (PrimitiveProfile.state w hw v phase (meshNode w v a b))
        (PrimitiveProfile.state w hw v phase (meshNode w v a 0)) := by
    induction b using Fin.induction with
    | zero => exact ⟨.refl,.refl⟩
    | succ b ih =>
      have hstep := vertical_mesh_edge_of_mouths w hw v ha hP hT phase hm a b
      exact ⟨ih.1.trans hstep.1,hstep.2.trans ih.2⟩
  exact ⟨(enter_mesh_origin w hw v ha phase).trans ((row x).1.trans (col x y).1),
    (col x y).2.trans ((row x).2.trans (leave_mesh_origin w hw v ha phase))⟩

end PushPuzzle.PushS.FiniteSourceInventory

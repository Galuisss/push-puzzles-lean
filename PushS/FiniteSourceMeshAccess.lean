/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshReach
public import PushS.FiniteSourceMouthFree
public import PushS.FiniteSourceLegal

/-! Every actual coarse-grid node is reachable from player zero under every literal normal primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Raster.width Raster.height

private theorem mesh_node_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1+1)) :
    NormalAnchorAccess w hw v phase (meshNode w v x y) :=
  mesh_node_access_of_mouths w hw v (admissible w hw v hP hT) hP hT phase (fun s => s.normal_mouths_free hP hT phase) x y

theorem vertical_low_shoulder_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w,tileStride w*y.val+padding w+(25*spacing w-(w+1)))) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have ha := admissible w hw v hP hT
  have hn := mesh_node_access w hw v hP hT phase x y.castSucc
  have hbefore := vertical_side_walk w hw v ha phase x y 0 (meshLow w) (meshLow_half w)
  have hbefore' := vertical_side_walk w hw v ha phase x y (meshLow w) 0 (meshLow_half w).symm
  rw [verticalSide_zero] at hbefore hbefore'
  have hjoin := vertical_low_shoulder_join w hw v ha phase x y q hq
  exact ⟨hn.1.trans (hbefore.trans hjoin.1),hjoin.2.trans (hbefore'.trans hn.2)⟩

theorem vertical_high_shoulder_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w,tileStride w*y.val+padding w+(25*spacing w+(w+1)))) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have ha := admissible w hw v hP hT
  have hn := mesh_node_access w hw v hP hT phase x y.succ
  have hafter := vertical_side_walk w hw v ha phase x y (meshHigh w) (Fin.last (tileStride w)) (meshHigh_half w)
  have hafter' := vertical_side_walk w hw v ha phase x y (Fin.last (tileStride w)) (meshHigh w) (meshHigh_half w).symm
  rw [verticalSide_last] at hafter hafter'
  have hjoin := vertical_high_shoulder_join w hw v ha phase x y q hq
  exact ⟨hn.1.trans (hafter'.trans hjoin.2),hjoin.1.trans (hafter.trans hn.2)⟩

theorem horizontal_low_shoulder_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w+(25*spacing w-(w+1)),tileStride w*y.val+padding w)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have ha := admissible w hw v hP hT
  have hn := mesh_node_access w hw v hP hT phase x.castSucc y
  have hbefore := horizontal_side_walk w hw v ha phase x y 0 (meshLow w) (meshLow_half w)
  have hbefore' := horizontal_side_walk w hw v ha phase x y (meshLow w) 0 (meshLow_half w).symm
  rw [horizontalSide_zero] at hbefore hbefore'
  have hjoin := horizontal_low_shoulder_join w hw v ha phase x y q hq
  exact ⟨hn.1.trans (hbefore.trans hjoin.1),hjoin.2.trans (hbefore'.trans hn.2)⟩

theorem horizontal_high_shoulder_access (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1)) (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*x.val+padding w+(25*spacing w+(w+1)),tileStride w*y.val+padding w)) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player) := by
  have ha := admissible w hw v hP hT
  have hn := mesh_node_access w hw v hP hT phase x.succ y
  have hafter := horizontal_side_walk w hw v ha phase x y (meshHigh w) (Fin.last (tileStride w)) (meshHigh_half w)
  have hafter' := horizontal_side_walk w hw v ha phase x y (Fin.last (tileStride w)) (meshHigh w) (meshHigh_half w).symm
  rw [horizontalSide_last] at hafter hafter'
  have hjoin := horizontal_high_shoulder_join w hw v ha phase x y q hq
  exact ⟨hn.1.trans (hafter'.trans hjoin.2),hjoin.1.trans (hafter.trans hn.2)⟩

end PushPuzzle.PushS.FiniteSourceInventory

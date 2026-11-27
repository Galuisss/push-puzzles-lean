/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshProducers
public import PushS.FiniteSourceMeshJoins

/-! Every actual used coarse edge has a literal same-stock detour through its real producing program's normal flip. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

private theorem vertical_producer_shoulder_coordinates {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (s : LineSite w hw v) (out : Direction) (haxis : out = .west ∨ out = .east)
    (hd : segmentDirection s.code.segment = out) (he : s.code.segment.finish = boundaryPoint w out)
    (gx gy : ℕ) (hbase : meshFaceBase out ((codes w v).get s.index).1 = (gx,gy)) (north : Bool) :
    coordinates (s.actualEmbedding.cells (s.endLane north)) =
      (tileStride w*gx+padding w,tileStride w*gy+padding w+shoulderOffset w out north) := by
  have hvertical : out = .east ∨ out = .west := haxis.symm
  have hh := s.producer_endLane_coordinates out hd he north
  rw [macro_shoulder,ite_eq_left hvertical,hbase] at hh
  exact hh

private theorem horizontal_producer_shoulder_coordinates {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (s : LineSite w hw v) (out : Direction) (haxis : out = .north ∨ out = .south)
    (hd : segmentDirection s.code.segment = out) (he : s.code.segment.finish = boundaryPoint w out)
    (gx gy : ℕ) (hbase : meshFaceBase out ((codes w v).get s.index).1 = (gx,gy)) (north : Bool) :
    coordinates (s.actualEmbedding.cells (s.endLane north)) =
      (tileStride w*gx+padding w+shoulderOffset w out north,tileStride w*gy+padding w) := by
  have hvertical : ¬(out = .east ∨ out = .west) := by rcases haxis with h | h <;> simp [h]
  have hh := s.producer_endLane_coordinates out hd he north
  rw [macro_shoulder,ite_eq_right hvertical,hbase] at hh
  exact hh

theorem vertical_used_mesh_crossing (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hm : ∀ s : LineSite w hw v, s.MouthsFree phase)
    (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1))
    (hu : CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .west) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshLow w)))
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshHigh w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshHigh w)))
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y (meshLow w))) := by
  obtain ⟨s,out,haxis,hd,he,_,hbase⟩ := vertical_used_producer w hw v hP hT x.val y.val hu
  have hlo := vertical_producer_shoulder_coordinates s out haxis hd he x.val y.val hbase (lowNorth out)
  have hhi := vertical_producer_shoulder_coordinates s out haxis hd he x.val y.val hbase (!(lowNorth out))
  rw [shoulderOffset_low] at hlo
  rw [shoulderOffset_high] at hhi
  have hlow := vertical_low_shoulder_join w hw v ha phase x y _ hlo
  have hhigh := vertical_high_shoulder_join w hw v ha phase x y _ hhi
  have hcross := s.normal_end_connected_of_mouths ha phase (hm s) (lowNorth out) (!(lowNorth out))
  have hback := s.normal_end_connected_of_mouths ha phase (hm s) (!(lowNorth out)) (lowNorth out)
  exact ⟨hlow.1.trans (hcross.trans hhigh.1),hhigh.2.trans (hback.trans hlow.2)⟩

theorem horizontal_used_mesh_crossing (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (hm : ∀ s : LineSite w hw v, s.MouthsFree phase)
    (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1))
    (hu : CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .north) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshLow w)))
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshHigh w))) ∧
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshHigh w)))
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y (meshLow w))) := by
  obtain ⟨s,out,haxis,hd,he,_,hbase⟩ := horizontal_used_producer w hw v hP hT x.val y.val hu
  have hlo := horizontal_producer_shoulder_coordinates s out haxis hd he x.val y.val hbase (lowNorth out)
  have hhi := horizontal_producer_shoulder_coordinates s out haxis hd he x.val y.val hbase (!(lowNorth out))
  rw [shoulderOffset_low] at hlo
  rw [shoulderOffset_high] at hhi
  have hlow := horizontal_low_shoulder_join w hw v ha phase x y _ hlo
  have hhigh := horizontal_high_shoulder_join w hw v ha phase x y _ hhi
  have hcross := s.normal_end_connected_of_mouths ha phase (hm s) (lowNorth out) (!(lowNorth out))
  have hback := s.normal_end_connected_of_mouths ha phase (hm s) (!(lowNorth out)) (lowNorth out)
  exact ⟨hlow.1.trans (hcross.trans hhigh.1),hhigh.2.trans (hback.trans hlow.2)⟩

end PushPuzzle.PushS.FiniteSourceInventory

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshLocalization
public import PushS.FiniteSourceMeshNodes

/-! Every unused coarse-grid edge is a complete literal same-stock corridor in the actual global board. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

private theorem vertical_unused_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .west)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro i hc p hp he
  exact vertical_unused_clear w v hP hT gx gy t ht hn _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band w hw _ _ hc p hp) (local_wall_collar_port w hw _ _ hc p hp)
    (he.trans hq)

private theorem horizontal_unused_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .north)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro i hc p hp he
  exact horizontal_unused_clear w v hP hT gx gy t ht hn _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band w hw _ _ hc p hp) (local_wall_collar_port w hw _ _ hc p hp)
    (he.trans hq)

private theorem vertical_unused_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .west)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hc := code_local w v _ (List.get_mem (codes w v) l.1)
  exact vertical_unused_clear w v hP hT gx gy t ht hn _ _
    (local_actor_bounds w hw _ (localCodes_fits w hw _ hc) goal l.2)
    (local_actor_collar_band w hw _ _ hc goal l.2) (local_actor_collar_port w hw _ _ hc goal l.2)
    ((normal_slot_coordinates w hw v goal l).symm.trans ((congrArg coordinates he).symm.trans hq))

private theorem horizontal_unused_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .north)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hc := code_local w v _ (List.get_mem (codes w v) l.1)
  exact horizontal_unused_clear w v hP hT gx gy t ht hn _ _
    (local_actor_bounds w hw _ (localCodes_fits w hw _ hc) goal l.2)
    (local_actor_collar_band w hw _ _ hc goal l.2) (local_actor_collar_port w hw _ _ hc goal l.2)
    ((normal_slot_coordinates w hw v goal l).symm.trans ((congrArg coordinates he).symm.trans hq))

private theorem vertical_unused_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .west)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨vertical_unused_floor w hw v hP hT gx gy t ht hn q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact vertical_unused_actor_ne w hw v hP hT gx gy t ht hn q hq (phase l.1) l he.symm

private theorem horizontal_unused_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (phase : Fin (codes w v).length → Bool)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hn : ¬CellPlan.Used (CellPlan.cell (v,(gx,gy))) .north)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨horizontal_unused_floor w hw v hP hT gx gy t ht hn q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact horizontal_unused_actor_ne w hw v hP hT gx gy t ht hn q hq (phase l.1) l he.symm

theorem vertical_unused_side_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (x : Fin (Raster.width v.1+1)) (y : Fin (Raster.height v.1))
    (hn : ¬CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .west) (a b : Fin (tileStride w+1)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y a))
      (PrimitiveProfile.state w hw v phase (verticalSide w v x y b)) := by
  apply walk_vertical (PrimitiveProfile.floor ha phase)
  intro z hz hz'
  let t := z.val-(tileStride w*y.val+padding w)
  have hbnd : min a.val b.val ≤ t ∧ t ≤ max a.val b.val := by
    dsimp [t,verticalSide] at *
    omega
  have ht : t ≤ tileStride w := by have ha' := a.isLt; have hb' := b.isLt; omega
  apply vertical_unused_free w hw v hP hT phase x.val y.val t ht hn
  apply Prod.ext
  · rfl
  · dsimp [coordinates,t]
    dsimp [verticalSide] at hz hz'
    omega

theorem horizontal_unused_side_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (x : Fin (Raster.width v.1)) (y : Fin (Raster.height v.1+1))
    (hn : ¬CellPlan.Used (CellPlan.cell (v,(x.val,y.val))) .north) (a b : Fin (tileStride w+1)) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y a))
      (PrimitiveProfile.state w hw v phase (horizontalSide w v x y b)) := by
  apply walk_horizontal (PrimitiveProfile.floor ha phase)
  intro z hz hz'
  let t := z.val-(tileStride w*x.val+padding w)
  have hbnd : min a.val b.val ≤ t ∧ t ≤ max a.val b.val := by
    dsimp [t,horizontalSide] at *
    omega
  have ht : t ≤ tileStride w := by have ha' := a.isLt; have hb' := b.isLt; omega
  apply horizontal_unused_free w hw v hP hT phase x.val y.val t ht hn
  apply Prod.ext
  · dsimp [coordinates,t]
    dsimp [horizontalSide] at hz hz'
    omega
  · rfl

end PushPuzzle.PushS.FiniteSourceInventory

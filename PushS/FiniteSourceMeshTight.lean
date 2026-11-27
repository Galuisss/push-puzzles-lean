/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMesh
public import PushS.FiniteRoutingMeshBandsTight

/-! Coarse-grid side shoulders at transverse distance `w+1` are actual normal-profile free cells. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

private theorem vertical_mesh_floor_tight (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hout : t+w < 25*spacing w ∨ 25*spacing w+w < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro i hc p hp he
  have hh := vertical_boundary_band w w (by unfold spacing; omega) gx gy t ht _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band_tight w hw _ _ hc p hp)
    (he.trans hq)
  omega

private theorem horizontal_mesh_floor_tight (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hout : t+w < 25*spacing w ∨ 25*spacing w+w < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro i hc p hp he
  have hh := horizontal_boundary_band w w (by unfold spacing; omega) gx gy t ht _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band_tight w hw _ _ hc p hp)
    (he.trans hq)
  omega

theorem vertical_mesh_free_tight (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+w < 25*spacing w ∨ 25*spacing w+w < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨vertical_mesh_floor_tight w hw v gx gy t ht hout q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact vertical_mesh_actor_ne_off_port w hw v gx gy t ht (by omega) q hq (phase l.1) l he.symm

theorem horizontal_mesh_free_tight (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+w < 25*spacing w ∨ 25*spacing w+w < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨horizontal_mesh_floor_tight w hw v gx gy t ht hout q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact horizontal_mesh_actor_ne_off_port w hw v gx gy t ht (by omega) q hq (phase l.1) l he.symm

end PushPuzzle.PushS.FiniteSourceInventory

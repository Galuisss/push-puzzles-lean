/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMeshBands
public import PushS.FiniteSourcePrimitiveProfile
public import PushS.FiniteSourceFloor
public import PushFS.Walking

/-! Actual coarse-grid side cells outside their narrow central port are free for every normal primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem port_band_index (w margin x y t a : ℕ)
    (hlo : margin < 25*spacing w) (ht : t ≤ tileStride w)
    (ha : padding w+25*spacing w ≤ a+margin ∧ a ≤ padding w+25*spacing w+margin)
    (he : tileStride w*x+a = tileStride w*y+padding w+t) :
    x = y ∧ 25*spacing w ≤ t+margin ∧ t ≤ 25*spacing w+margin := by
  have hhi : 25*spacing w+margin < tileStride w := by unfold tileStride; omega
  have hxy : x = y := by
    rcases lt_trichotomy x y with h | h | h
    · have hm := Nat.mul_le_mul_left (tileStride w) (show x+1 ≤ y by omega)
      rw [Nat.mul_add,Nat.mul_one] at hm
      omega
    · exact h
    · have hm := Nat.mul_le_mul_left (tileStride w) (show y+1 ≤ x by omega)
      rw [Nat.mul_add,Nat.mul_one] at hm
      omega
  subst x
  exact ⟨rfl,by omega,by omega⟩

/-- A padded grid boundary belongs to its current macrocell or its predecessor. -/
theorem boundary_axis_origins (w gx r a : ℕ) (ha : a < tileSide w)
    (he : tileStride w*r+a = tileStride w*gx+padding w) :
    (r = gx ∧ a ≤ 2*padding w) ∨ (r+1 = gx ∧ tileStride w ≤ a) := by
  have hclose := macro_axis_close w gx r (padding w) a (by unfold tileSide; omega) ha he.symm
  have hr : r ≤ gx := by
    by_contra hh
    have hm := Nat.mul_le_mul_left (tileStride w) (show gx+1 ≤ r by omega)
    rw [Nat.mul_add,Nat.mul_one] at hm
    have hpad : padding w < tileStride w := by unfold padding tileStride spacing; omega
    omega
  by_cases h : r = gx
  · exact Or.inl ⟨h,by rw [h] at he; omega⟩
  · have hs : r+1 = gx := by omega
    refine Or.inr ⟨hs,?_⟩
    rw [←hs,Nat.mul_add,Nat.mul_one] at he
    omega

theorem vertical_boundary_band (w margin : ℕ) (hm : margin < 25*spacing w)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (r a : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w margin face a)
    (he : macroShift w r a = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    25*spacing w ≤ t+margin ∧ t ≤ 25*spacing w+margin := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*r.1+a.1 = tileStride w*gx+padding w at hx
  change tileStride w*r.2+a.2 = tileStride w*gy+padding w+t at hy
  have hcases := boundary_axis_origins w gx r.1 a.1 ha.1 hx
  have hb : padding w+25*spacing w ≤ a.2+margin ∧ a.2 ≤ padding w+25*spacing w+margin := by
    rcases hcases with h | h
    · exact hband .west h.2
    · exact hband .east h.2
  exact (port_band_index w margin r.2 gy t a.2 hm ht hb hy).2

theorem horizontal_boundary_band (w margin : ℕ) (hm : margin < 25*spacing w)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (r a : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w)
    (hband : ∀ face, InCollar w face a → PortBand w margin face a)
    (he : macroShift w r a = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    25*spacing w ≤ t+margin ∧ t ≤ 25*spacing w+margin := by
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  change tileStride w*r.1+a.1 = tileStride w*gx+padding w+t at hx
  change tileStride w*r.2+a.2 = tileStride w*gy+padding w at hy
  have hcases := boundary_axis_origins w gy r.2 a.2 ha.2 hy
  have hb : padding w+25*spacing w ≤ a.1+margin ∧ a.1 ≤ padding w+25*spacing w+margin := by
    rcases hcases with h | h
    · exact hband .north h.2
    · exact hband .south h.2
  exact (port_band_index w margin r.1 gx t a.1 hm ht hb hx).2

/-- Pointwise clearance from each emitted wall patch gives floor in their actual global union. -/
theorem mesh_floor_of_local_clear (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (q : Cell (width w v) (height w v))
    (hclear : ∀ (i : Fin (codes w v).length),
      ((codes w v).get i).2 ∈ localCodes w (CellPlan.cell (v,((codes w v).get i).1)) → ∀
      (p : Cell (((codes w v).get i).2.instanceOf w hw).width (((codes w v).get i).2.instanceOf w hw).height),
      p ∈ (((codes w v).get i).2.instanceOf w hw).board.walls →
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.world w hw p) ≠ coordinates q) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨i,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  exact hclear i (code_local w v _ (List.get_mem (codes w v) i)) p hp ((placed_wall_coordinates w hw v i p).symm.trans (congrArg coordinates he))

private theorem vertical_mesh_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro j hc p hp he
  have hband := vertical_boundary_band w (w+1) (by unfold spacing; omega) gx gy t ht _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band w hw _ _ hc p hp)
    (he.trans hq)
  omega

private theorem horizontal_mesh_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    q ∉ (inventory w hw v).walls := by
  apply mesh_floor_of_local_clear w hw v q
  intro j hc p hp he
  have hband := horizontal_boundary_band w (w+1) (by unfold spacing; omega) gx gy t ht _ _
    (local_world_bounds w hw _ (localCodes_fits w hw _ hc) p)
    (local_wall_collar_band w hw _ _ hc p hp)
    (he.trans hq)
  omega

theorem normal_slot_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    coordinates (if goal then (inventory w hw v).target l else (inventory w hw v).source l) =
      macroShift w ((codes w v).get l.1).1 (((codes w v).get l.1).2.actor w hw goal l.2) := by
  rcases l with ⟨i,l⟩
  cases goal
  · exact placed_source_coordinates w hw v i l
  · exact placed_target_coordinates w hw v i l

private theorem normal_actor_band (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (margin : ℕ)
    (i : Fin (codes w v).length) (goal : Bool) (l : Label w v i) (face : Direction)
    (hf : InCollar w face (((codes w v).get i).2.actor w hw goal l)) :
    PortBand w margin face (((codes w v).get i).2.actor w hw goal l) := by
  have hc := code_local w v _ (List.get_mem (codes w v) i)
  have hl := local_actor_collar_lane w hw _ _ hc goal l face hf
  cases face <;> dsimp [PortBand,SameLane,Line.along,boundaryPoint] at hl ⊢ <;> omega

private theorem vertical_normal_band (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (margin : ℕ)
    (hm : margin < 25*spacing w) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel)
    (he : coordinates (if goal then (inventory w hw v).target l else (inventory w hw v).source l) =
      (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    25*spacing w ≤ t+margin ∧ t ≤ 25*spacing w+margin := by
  have hc := code_local w v _ (List.get_mem (codes w v) l.1)
  exact vertical_boundary_band w margin hm gx gy t ht _ _
    (local_actor_bounds w hw _ (localCodes_fits w hw _ hc) goal l.2)
    (normal_actor_band w hw v margin l.1 goal l.2)
    ((normal_slot_coordinates w hw v goal l).symm.trans he)

private theorem horizontal_normal_band (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (margin : ℕ)
    (hm : margin < 25*spacing w) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel)
    (he : coordinates (if goal then (inventory w hw v).target l else (inventory w hw v).source l) =
      (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    25*spacing w ≤ t+margin ∧ t ≤ 25*spacing w+margin := by
  have hc := code_local w v _ (List.get_mem (codes w v) l.1)
  exact horizontal_boundary_band w margin hm gx gy t ht _ _
    (local_actor_bounds w hw _ (localCodes_fits w hw _ hc) goal l.2)
    (normal_actor_band w hw v margin l.1 goal l.2)
    ((normal_slot_coordinates w hw v goal l).symm.trans he)

private theorem vertical_mesh_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hh := vertical_normal_band w hw v (w+1) (by unfold spacing; omega) gx gy t ht goal l
    ((congrArg coordinates he).symm.trans hq)
  omega

private theorem horizontal_mesh_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hh := horizontal_normal_band w hw v (w+1) (by unfold spacing; omega) gx gy t ht goal l
    ((congrArg coordinates he).symm.trans hq)
  omega

theorem vertical_mesh_actor_ne_off_port (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hne : t ≠ 25*spacing w)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hh := vertical_normal_band w hw v 0 (by unfold spacing; omega) gx gy t ht goal l
    ((congrArg coordinates he).symm.trans hq)
  omega

theorem horizontal_mesh_actor_ne_off_port (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (gx gy t : ℕ) (ht : t ≤ tileStride w) (hne : t ≠ 25*spacing w)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w))
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  intro he
  have hh := horizontal_normal_band w hw v 0 (by unfold spacing; omega) gx gy t ht goal l
    ((congrArg coordinates he).symm.trans hq)
  omega

theorem vertical_mesh_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w,tileStride w*gy+padding w+t)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨vertical_mesh_floor w hw v gx gy t ht hout q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact vertical_mesh_actor_ne w hw v gx gy t ht hout q hq (phase l.1) l he.symm

theorem horizontal_mesh_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (gx gy t : ℕ) (ht : t ≤ tileStride w)
    (hout : t+(w+1) < 25*spacing w ∨ 25*spacing w+(w+1) < t)
    (q : Cell (width w v) (height w v))
    (hq : coordinates q = (tileStride w*gx+padding w+t,tileStride w*gy+padding w)) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨horizontal_mesh_floor w hw v gx gy t ht hout q hq,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact horizontal_mesh_actor_ne w hw v gx gy t ht hout q hq (phase l.1) l he.symm

end PushPuzzle.PushS.FiniteSourceInventory

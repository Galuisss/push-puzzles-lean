/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMeshWalks

/-! Every normal whole-board profile has literal same-stock walks from player zero to the coarse-grid origin. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height

/-- Same-stock player walks from the actual exterior anchor to a point and back. -/
@[expose] def NormalAnchorAccess (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (q : Cell (width w v) (height w v)) : Prop :=
  Reachable (inventory w hw v).board (some 1)
    (PrimitiveProfile.state w hw v phase (inventory w hw v).player) (PrimitiveProfile.state w hw v phase q) ∧
  Reachable (inventory w hw v).board (some 1)
    (PrimitiveProfile.state w hw v phase q) (PrimitiveProfile.state w hw v phase (inventory w hw v).player)

private theorem corner_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (q : Cell (width w v) (height w v)) (hx : q.1.val ≤ padding w) (hy : q.2.val ≤ padding w) :
    q ∉ (inventory w hw v).walls := by
  intro hm
  obtain ⟨i,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have hc := code_local w v _ (List.get_mem (codes w v) i)
  have hh := (placed_wall_coordinates w hw v i p).symm.trans (congrArg coordinates he)
  have hxx := congrArg Prod.fst hh
  have hyy := congrArg Prod.snd hh
  dsimp [macroShift,coordinates] at hxx hyy
  change tileStride w*((codes w v).get i).1.1+(((codes w v).get i).2.world w hw p).1 = q.1.val at hxx
  change tileStride w*((codes w v).get i).1.2+(((codes w v).get i).2.world w hw p).2 = q.2.val at hyy
  have hl := local_wall_collar_band w hw _ _ hc p hp .west (by change _ ≤ 2*padding w; omega)
  dsimp [PortBand] at hl
  change padding w+25*spacing w ≤ (((codes w v).get i).2.world w hw p).2+(w+1) ∧
    (((codes w v).get i).2.world w hw p).2 ≤ padding w+25*spacing w+(w+1) at hl
  unfold spacing at hl
  omega

private theorem corner_actor_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (q : Cell (width w v) (height w v)) (hx : q.1.val ≤ padding w) (hy : q.2.val ≤ padding w)
    (goal : Bool) (l : (inventory w hw v).PhysicalLabel) :
    q ≠ if goal then (inventory w hw v).target l else (inventory w hw v).source l := by
  rcases l with ⟨i,l⟩
  intro he
  have hc := code_local w v _ (List.get_mem (codes w v) i)
  have hh : macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw goal l) = coordinates q := by
    cases goal
    · exact (placed_source_coordinates w hw v i l).symm.trans (congrArg coordinates he).symm
    · exact (placed_target_coordinates w hw v i l).symm.trans (congrArg coordinates he).symm
  have hxx := congrArg Prod.fst hh
  have hyy := congrArg Prod.snd hh
  dsimp [macroShift,coordinates] at hxx hyy
  change tileStride w*((codes w v).get i).1.1+(((codes w v).get i).2.actor w hw goal l).1 = q.1.val at hxx
  change tileStride w*((codes w v).get i).1.2+(((codes w v).get i).2.actor w hw goal l).2 = q.2.val at hyy
  have hl := local_actor_collar_lane w hw _ _ hc goal l .west (by change _ ≤ 2*padding w; omega)
  dsimp [SameLane,Line.along,boundaryPoint] at hl
  change padding w+25*spacing w = (((codes w v).get i).2.actor w hw goal l).2 at hl
  unfold spacing at hl
  omega

private theorem corner_free (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (phase : Fin (codes w v).length → Bool) (q : Cell (width w v) (height w v))
    (hx : q.1.val ≤ padding w) (hy : q.2.val ≤ padding w) :
    Free (inventory w hw v).board (PrimitiveProfile.boxes w hw v phase) q := by
  refine ⟨corner_floor w hw v q hx hy,?_⟩
  intro hp
  obtain ⟨l,_,he⟩ := Finset.mem_image.mp hp
  exact corner_actor_ne w hw v q hx hy (phase l.1) l he.symm

private theorem corner_walk (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool)
    (p q : Cell (width w v) (height w v)) (hpx : p.1.val ≤ padding w) (hpy : p.2.val ≤ padding w)
    (hqx : q.1.val ≤ padding w) (hqy : q.2.val ≤ padding w) :
    Reachable (inventory w hw v).board (some 1) (PrimitiveProfile.state w hw v phase p) (PrimitiveProfile.state w hw v phase q) := by
  have hboxes := PrimitiveProfile.floor ha phase
  have h1 := walk_horizontal hboxes p.1 q.1 p.2 (fun x _ hx => corner_free w hw v phase (x,p.2) (by change x.val ≤ padding w; omega) hpy)
  have h2 := walk_vertical hboxes q.1 p.2 q.2 (fun y _ hy => corner_free w hw v phase (q.1,y) hqx (by change y.val ≤ padding w; omega))
  exact h1.trans h2

/-- The first padded coarse-grid vertex reached from player zero. -/
@[expose] def meshOrigin (w : ℕ) (v : CellPlan.Source) : Cell (width w v) (height w v) :=
  (⟨padding w,by unfold width; omega⟩,⟨padding w,by unfold height; omega⟩)

theorem enter_mesh_origin (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player)
      (PrimitiveProfile.state w hw v phase (meshOrigin w v)) :=
  corner_walk w hw v ha phase _ _ (by change 0 ≤ padding w; omega) (by change 0 ≤ padding w; omega) (le_refl _) (le_refl _)

theorem leave_mesh_origin (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (ha : (inventory w hw v).Admissible) (phase : Fin (codes w v).length → Bool) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (meshOrigin w v))
      (PrimitiveProfile.state w hw v phase (inventory w hw v).player) :=
  corner_walk w hw v ha phase _ _ (le_refl _) (le_refl _) (by change 0 ≤ padding w; omega) (by change 0 ≤ padding w; omega)

end PushPuzzle.PushS.FiniteSourceInventory

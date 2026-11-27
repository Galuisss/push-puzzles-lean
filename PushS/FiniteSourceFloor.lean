/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMacroGeometry

/-! Every real globally emitted normal source and target actor avoids the full wall union. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem cells_entry (v : CellPlan.Source) (entry : GridRouting.Point × CellPlan.Code)
    (he : entry ∈ CellPlan.cells v) : entry.2 = CellPlan.cell (v,entry.1) := by
  rcases entry with ⟨⟨x,y⟩,code⟩
  simp only [CellPlan.cells,List.mem_flatMap,List.mem_map,List.mem_range,Prod.mk.injEq] at he
  obtain ⟨y',_,x',_,⟨⟨rfl,rfl⟩,he⟩⟩ := he
  exact he.symm

theorem code_local (w : ℕ) (v : CellPlan.Source) (q : GridRouting.Point × PrimitiveCode)
    (hq : q ∈ codes w v) : q.2 ∈ localCodes w (CellPlan.cell (v,q.1)) := by
  unfold codes at hq
  obtain ⟨entry,hentry,hq⟩ := List.mem_flatMap.mp hq
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hq
  rw [cells_entry v entry hentry] at hp
  exact hp

private theorem localCodes_wall_clear (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code)
    (c d : PrimitiveCode)
    (hc : c ∈ localCodes w code) (hd : d ∈ localCodes w code) : ActorWallsClear w hw c d := by
  cases code with
  | none => simp [localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gateCodes_wall_clear w hw g.2 c hc d hd
    | inr q => exact (wireSpec w q.2).codes_wall_clear w hw (wireSpec_geometry w q.2) c hc d hd

private theorem primitive_actor_wall_ne (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (q t : GridRouting.Point × PrimitiveCode) (hq : q ∈ codes w v) (ht : t ∈ codes w v)
    (goal : Bool) (l : q.2.Labels w)
    (p : Cell (t.2.instanceOf w hw).width (t.2.instanceOf w hw).height)
    (hp : p ∈ (t.2.instanceOf w hw).board.walls) :
    macroShift w q.1 (q.2.actor w hw goal l) ≠ macroShift w t.1 (t.2.world w hw p) := by
  have hql := code_local w v q hq
  have htl := code_local w v t ht
  apply macro_actor_wall_ne w q.1 t.1 _ _
    (local_actor_bounds w hw q.2 (localCodes_fits w hw _ hql) goal l)
    (local_world_bounds w hw t.2 (localCodes_fits w hw _ htl) p)
    (local_actor_collar_lane w hw _ q.2 hql goal l)
    (local_wall_collar_off_lane w hw _ t.2 htl p hp)
  intro hpos
  apply localCodes_wall_clear w hw (CellPlan.cell (v,q.1)) q.2 t.2 hql _ goal l p hp
  simpa only [hpos] using htl

theorem placed_source_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (l : Label w v i) :
    coordinates ((inventory w hw v).source ⟨i,l⟩) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw false l) := by
  apply Prod.ext
  · change (tileStride w*((codes w v).get i).1.1+((codes w v).get i).2.offsetX w)+
      ((((codes w v).get i).2.matching w hw).source l).1.val = _
    exact Nat.add_assoc _ _ _
  · change (tileStride w*((codes w v).get i).1.2+((codes w v).get i).2.offsetY w)+
      ((((codes w v).get i).2.matching w hw).source l).2.val = _
    exact Nat.add_assoc _ _ _

theorem placed_target_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (l : Label w v i) :
    coordinates ((inventory w hw v).target ⟨i,l⟩) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw true l) := by
  apply Prod.ext
  · change (tileStride w*((codes w v).get i).1.1+((codes w v).get i).2.offsetX w)+
      ((((codes w v).get i).2.matching w hw).target l).1.val = _
    exact Nat.add_assoc _ _ _
  · change (tileStride w*((codes w v).get i).1.2+((codes w v).get i).2.offsetY w)+
      ((((codes w v).get i).2.matching w hw).target l).2.val = _
    exact Nat.add_assoc _ _ _

theorem placed_wall_coordinates (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source) (i : Fin (codes w v).length)
    (p : Cell ((inventory w hw v).piece i).width ((inventory w hw v).piece i).height) :
    coordinates (((inventory w hw v).embedding i).cells p) =
      macroShift w ((codes w v).get i).1 (((codes w v).get i).2.world w hw p) := by
  apply Prod.ext
  · change (tileStride w*((codes w v).get i).1.1+((codes w v).get i).2.offsetX w)+p.1.val = _
    exact Nat.add_assoc _ _ _
  · change (tileStride w*((codes w v).get i).1.2+((codes w v).get i).2.offsetY w)+p.2.val = _
    exact Nat.add_assoc _ _ _

theorem source_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (l : (inventory w hw v).PhysicalLabel) : (inventory w hw v).source l ∉ (inventory w hw v).walls := by
  rcases l with ⟨i,l⟩
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have he' := congrArg coordinates he
  rw [placed_wall_coordinates,placed_source_coordinates] at he'
  exact primitive_actor_wall_ne w hw v _ _ (List.get_mem _ _) (List.get_mem _ _) false l p hp he'.symm

theorem target_floor (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (l : (inventory w hw v).PhysicalLabel) : (inventory w hw v).target l ∉ (inventory w hw v).walls := by
  rcases l with ⟨i,l⟩
  intro hm
  obtain ⟨j,_,hm⟩ := Finset.mem_biUnion.mp hm
  obtain ⟨p,hp,he⟩ := Finset.mem_map.mp hm
  have he' := congrArg coordinates he
  rw [placed_wall_coordinates,placed_target_coordinates] at he'
  exact primitive_actor_wall_ne w hw v _ _ (List.get_mem _ _) (List.get_mem _ _) true l p hp he'.symm

end PushPuzzle.PushS.FiniteSourceInventory

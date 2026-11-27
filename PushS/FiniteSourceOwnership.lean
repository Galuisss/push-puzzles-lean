/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceSeparation

/-! The actual flattened source primitive emitter owns every normal box exactly once. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL

attribute [local irreducible] codes width height Raster.width Raster.height Line.width Line.height Line.walls

def PlacedActorsApart (w : ℕ) (hw : 2 ≤ w) (q t : GridRouting.Point × PrimitiveCode) : Prop :=
  ∀ (goal : Bool) (l : q.2.Labels w) (s : t.2.Labels w),
    macroShift w q.1 (q.2.actor w hw goal l) ≠ macroShift w t.1 (t.2.actor w hw goal s)

theorem macroShift_injective (w : ℕ) (p : ℕ × ℕ) : Function.Injective (macroShift w p) := by
  intro a b he
  have hx := congrArg Prod.fst he
  have hy := congrArg Prod.snd he
  exact Prod.ext (Nat.add_left_cancel hx) (Nat.add_left_cancel hy)

private theorem localCodes_pairwise (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) :
    (localCodes w code).Pairwise (ActorsApart w hw) := by
  cases code with
  | none => simp [localCodes]
  | some code =>
    cases code with
    | inl g => exact gateCodes_pairwise w hw g.2
    | inr q => exact (wireSpec w q.2).codes_pairwise w hw (wireSpec_geometry w q.2)

theorem cells_positions_pairwise (v : CellPlan.Source) :
    (CellPlan.cells v).Pairwise (fun a b => a.1 ≠ b.1) := by
  unfold CellPlan.cells
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro y _
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ List.pairwise_lt_range
    intro x z hxz he
    exact Nat.ne_of_lt hxz (congrArg Prod.fst he)
  · apply List.Pairwise.imp _ List.pairwise_lt_range
    intro y z hyz a ha b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp ha
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hb
    intro he
    exact Nat.ne_of_lt hyz (congrArg Prod.snd he)

private theorem codes_pairwise (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (codes w v).Pairwise (PlacedActorsApart w hw) := by
  unfold codes
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro entry _
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ (localCodes_pairwise w hw entry.2)
    intro c d hcd goal l s he
    exact hcd goal l s (macroShift_injective w entry.1 he)
  · apply List.Pairwise.imp_of_mem _ (cells_positions_pairwise v)
    intro entry other he ho hpos q hq t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp ht
    intro goal l s
    apply foreign_actor_ne w hw v hP hT (entry.1,c) (other.1,d) _ _ hpos goal l s
    · unfold codes
      exact List.mem_flatMap.mpr ⟨entry,he,List.mem_map.mpr ⟨c,hc,rfl⟩⟩
    · unfold codes
      exact List.mem_flatMap.mpr ⟨other,ho,List.mem_map.mpr ⟨d,hd,rfl⟩⟩

private theorem chosen_injective (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (goal : Bool) :
    Function.Injective (fun l : (inventory w hw v).PhysicalLabel =>
      if goal then (inventory w hw v).target l else (inventory w hw v).source l) := by
  intro ⟨i,l⟩ ⟨j,s⟩ he
  by_cases hij : i = j
  · subst j
    cases goal
    · have hl := ((inventory w hw v).matching i).source.injective
        (((inventory w hw v).embedding i).cells.injective he)
      exact congrArg (Sigma.mk i) hl
    · have hl := ((inventory w hw v).matching i).target.injective
        (((inventory w hw v).embedding i).cells.injective he)
      exact congrArg (Sigma.mk i) hl
  · have he' : macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw goal l) =
        macroShift w ((codes w v).get j).1 (((codes w v).get j).2.actor w hw goal s) := by
      cases goal
      · have hh := congrArg coordinates he
        simp only [Bool.false_eq_true,↓reduceIte] at hh
        rw [placed_source_coordinates,placed_source_coordinates] at hh
        exact hh
      · have hh := congrArg coordinates he
        simp only [↓reduceIte] at hh
        rw [placed_target_coordinates,placed_target_coordinates] at hh
        exact hh
    have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hval with hlt | hlt
    · have h := List.pairwise_iff_getElem.mp (codes_pairwise w hw v hP hT) i.val j.val i.isLt j.isLt hlt
      exact (h goal l s he').elim
    · have h := List.pairwise_iff_getElem.mp (codes_pairwise w hw v hP hT) j.val i.val j.isLt i.isLt hlt
      exact (h goal s l he'.symm).elim

private theorem source_injective (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Function.Injective (inventory w hw v).source := chosen_injective w hw v hP hT false

private theorem target_injective (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    Function.Injective (inventory w hw v).target := chosen_injective w hw v hP hT true

/-- All four box ownership and floor fields of the concrete global source inventory. -/
theorem inventory_actorsClear (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) : InventoryActorsClear (inventory w hw v) :=
  ⟨source_injective w hw v hP hT,target_injective w hw v hP hT,source_floor w hw v,target_floor w hw v⟩

end PushPuzzle.PushS.FiniteSourceInventory

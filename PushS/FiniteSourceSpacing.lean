/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePortSpacing
public import PushS.FiniteSourceOwnership
public import PushS.FiniteRoutingGateSpacing

/-! Normal targets owned by different actual emitted primitives are never adjacent. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

def PlacedActorsSparse (w : ℕ) (hw : 2 ≤ w) (q t : (ℕ × ℕ) × PrimitiveCode) : Prop :=
  ∀ (goal : Bool) (l : q.2.Labels w) (s : t.2.Labels w) (d : Direction),
    ¬Travels d (macroShift w q.1 (q.2.actor w hw goal l))
      (macroShift w t.1 (t.2.actor w hw goal s)) 1

private theorem localCodes_sparse (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) :
    (localCodes w code).Pairwise (ActorsSparse w hw) := by
  cases code with
  | none => simp [localCodes]
  | some code =>
    cases code with
    | inl g => exact gateCodes_sparse w hw g.2
    | inr q => exact wireCodes_sparse w hw q.2

private theorem codes_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    (codes w v).Pairwise (PlacedActorsSparse w hw) := by
  unfold codes
  apply List.pairwise_flatMap.mpr
  refine ⟨?_,?_⟩
  · intro entry _
    apply List.pairwise_map.mpr
    apply List.Pairwise.imp _ (localCodes_sparse w hw entry.2)
    intro c t hct goal l s d he
    exact hct goal l s d ((shift_travels_iff (tileStride w*entry.1.1,tileStride w*entry.1.2) d _ _).mp he)
  · apply List.Pairwise.imp_of_mem _ (cells_positions_pairwise v)
    intro entry other he ho hpos q hq t ht
    obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hq
    obtain ⟨e,he',rfl⟩ := List.mem_map.mp ht
    intro goal l s d hadj
    apply foreign_actor_sparse w hw v hP hT (entry.1,c) (other.1,e) _ _ hpos goal l s
      (travels_one_nearby hadj)
    · unfold codes
      exact List.mem_flatMap.mpr ⟨entry,he,List.mem_map.mpr ⟨c,hc,rfl⟩⟩
    · unfold codes
      exact List.mem_flatMap.mpr ⟨other,ho,List.mem_map.mpr ⟨e,he',rfl⟩⟩

theorem normal_primitive_sparse (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i j : Fin (codes w v).length) (hij : i ≠ j) (goal : Bool)
    (l : Label w v i) (s : Label w v j) (d : Direction) :
    ¬Adjacent d
      (if goal then (inventory w hw v).target ⟨i,l⟩ else (inventory w hw v).source ⟨i,l⟩)
      (if goal then (inventory w hw v).target ⟨j,s⟩ else (inventory w hw v).source ⟨j,s⟩) := by
  intro hadj
  have hh := adjacent_coordinates hadj
  have he : Travels d
      (macroShift w ((codes w v).get i).1 (((codes w v).get i).2.actor w hw goal l))
      (macroShift w ((codes w v).get j).1 (((codes w v).get j).2.actor w hw goal s)) 1 := by
    cases goal
    · simp only [Bool.false_eq_true,↓reduceIte] at hh
      rw [placed_source_coordinates,placed_source_coordinates] at hh
      exact hh
    · simp only [↓reduceIte] at hh
      rw [placed_target_coordinates,placed_target_coordinates] at hh
      exact hh
  have hval : i.val ≠ j.val := fun h => hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hlt
  · have h := List.pairwise_iff_getElem.mp (codes_sparse w hw v hP hT) i.val j.val i.isLt j.isLt hlt
    exact h goal l s d he
  · have h := List.pairwise_iff_getElem.mp (codes_sparse w hw v hP hT) j.val i.val j.isLt i.isLt hlt
    exact h goal s l d.opposite (travels_one_reverse he)

end PushPuzzle.PushS.FiniteSourceInventory

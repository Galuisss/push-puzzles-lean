/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePrimitiveProfile

/-! Idle actual compiler owners may be marked complete without changing any real box. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

/-- An idle primitive has exactly the same literal source and target identity slots. -/
private theorem source_target_idle (l : (inventory w hw v).PhysicalLabel)
    (hc : (((codes w v).get l.1).2).SamePhase) :
    (inventory w hw v).source l = (inventory w hw v).target l := by
  rcases l with ⟨i,l⟩
  apply congrArg ((inventory w hw v).embedding i).cells
  unfold inventory
  exact PrimitiveCode.matching_samePhase w hw _ hc l

/-- Phase functions that differ only on genuinely idle compiler primitives give the same complete real stock. -/
private theorem boxes_congr (a b : Fin (codes w v).length → Bool)
    (h : ∀ i,a i = b i ∨ (((codes w v).get i).2).SamePhase) : boxes w hw v a = boxes w hw v b := by
  unfold boxes
  congr 1
  funext l
  rcases h l.1 with he | hi
  · simp only [position,he]
  · simp only [position,source_target_idle l hi,ite_self]

/-- Marking any additional idle owners complete preserves the entire actual player state. -/
theorem state_congr (a b : Fin (codes w v).length → Bool)
    (h : ∀ i,a i = b i ∨ (((codes w v).get i).2).SamePhase)
    (player : Cell (width w v) (height w v)) : state w hw v a player = state w hw v b player := by
  exact congrArg (fun stock => (⟨player,stock⟩ : State (width w v) (height w v))) (boxes_congr a b h)

/-- A source tile whose actual emitted primitives are all idle changes no literal player state. -/
theorem tile_update_idle (phase : GridRouting.Point → Bool) (p : GridRouting.Point)
    (idle : ∀ code ∈ localCodes w (CellPlan.cell (v,p)),code.SamePhase) :
    profileState w hw v phase = profileState w hw v (Function.update phase p true) := by
  change state w hw v (fun i => phase ((codes w v).get i).1) (inventory w hw v).player =
    state w hw v (fun i => Function.update phase p true ((codes w v).get i).1) (inventory w hw v).player
  apply state_congr
  intro i
  by_cases hp : ((codes w v).get i).1 = p
  · apply Or.inr
    apply idle
    have hc := code_local w v ((codes w v).get i) (List.get_mem _ _)
    rw [hp] at hc
    exact hc
  · exact Or.inl (Function.update_of_ne hp _ _).symm

end PushPuzzle.PushS.FiniteSourceInventory.PrimitiveProfile

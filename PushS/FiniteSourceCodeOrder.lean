/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourcePathSites
public import PushS.FiniteSourceLegal
public import PushS.FiniteRoutingLineNeighbors

/-! Actual primitive tables have distinct entries and preserve every path instruction order. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting
open Cslib.Complexity.NCL
open scoped Classical

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height inventory Line.width Line.height Line.program Line.positions

/-- A literal working identity exists in every emitted primitive. -/
def primitiveWitness (c : PrimitiveCode) : c.Labels w := by
  cases c with
  | core g =>
    cases h : g.core.isAND
    · exact (show (PrimitiveCode.core g).Labels w from by simpa only [PrimitiveCode.Labels,h] using (FiniteGeometry.OrLabel.triggerA : FiniteGeometry.OrLabel w))
    · exact (show (PrimitiveCode.core g).Labels w from by simpa only [PrimitiveCode.Labels,h] using (FiniteGeometry.AndLabel.triggerA : FiniteGeometry.AndLabel w))
  | line c =>
    refine ⟨Line.secondLabel w (segmentLength c.segment) (c.above != c.desiredSide),Or.inr ?_,Or.inr ?_⟩
    · change 0 < 1
      omega
    · change 1+1 < _
      have hn := Line.program_length_ge_six w (segmentLength c.segment) (c.above != c.desiredSide)
      omega
  | turn _ => exact (0 : Fin 2)

/-- An emitted local identity retains its literal primitive owner index. -/
theorem primitiveLabel_owner (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)
    (i : Fin (codes w v).length) (c : PrimitiveCode) (hc : ((codes w v).get i).2 = c) (l : c.Labels w) :
    (primitiveLabel w hw v i c hc l).1 = i := by
  subst c
  rfl

/-- Repeated actual table entries would duplicate their literal working box. -/
theorem code_get_injective (ha : (inventory w hw v).Admissible) :
    Function.Injective (fun i : Fin (codes w v).length => (codes w v).get i) := by
  intro i j he
  let c := ((codes w v).get i).2
  let l := primitiveWitness (w := w) c
  let x := primitiveLabel w hw v i c rfl l
  let y := primitiveLabel w hw v j c (congrArg Prod.snd he.symm) l
  have hs : (inventory w hw v).source x = (inventory w hw v).source y := by
    apply Prod.ext <;> apply Fin.ext
    all_goals
      have hx := source_primitiveLabel_coordinates w hw v i c rfl l
      have hy := source_primitiveLabel_coordinates w hw v j c (congrArg Prod.snd he.symm) l
      have hc := congrArg (fun entry : GridRouting.Point × PrimitiveCode =>
        shiftPoint (tileStride w*entry.1.1) (tileStride w*entry.1.2) (c.actor w hw false l)) he
      first
      | exact congrArg Prod.fst (hx.trans (hc.trans hy.symm))
      | exact congrArg Prod.snd (hx.trans (hc.trans hy.symm))
  have hl := congrArg Sigma.fst (ha.source_injective hs)
  exact (primitiveLabel_owner w hw v i c rfl l).symm.trans (hl.trans (primitiveLabel_owner w hw v j c _ l))

end PushPuzzle.PushS.FiniteSourceInventory

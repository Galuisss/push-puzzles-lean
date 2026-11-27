/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceInventory
public import PushS.FiniteRoutingLineCompletion
public import PushS.FiniteRoutingPathReadout

/-! Actual compiled primitive labels and placements, with dependent code equalities hidden from glyph consumers. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

attribute [local irreducible] width height codes

def primitiveLabel (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (l : c.Labels w) : (inventory w hw v).PhysicalLabel := by
  subst c
  exact ⟨i,l⟩

def primitiveEmbedding (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) :
    GridEmbedding (c.instanceOf w hw).width (c.instanceOf w hw).height (width w v) (height w v) := by
  subst c
  exact (inventory w hw v).embedding i

theorem primitiveLabel_injective (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) : Function.Injective (primitiveLabel w hw v i c he) := by
  subst c
  exact (inventory w hw v).labelEmbedding i |>.injective

theorem source_primitiveLabel (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (l : c.Labels w) :
    (inventory w hw v).source (primitiveLabel w hw v i c he l) =
      (primitiveEmbedding w hw v i c he).cells ((c.matching w hw).source l) := by
  subst c
  rfl

theorem target_primitiveLabel (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (l : c.Labels w) :
    (inventory w hw v).target (primitiveLabel w hw v i c he l) =
      (primitiveEmbedding w hw v i c he).cells ((c.matching w hw).target l) := by
  subst c
  rfl

theorem wall_primitiveEmbedding (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (primitiveEmbedding w hw v i c he).cells p ∈ (inventory w hw v).walls := by
  subst c
  apply Finset.mem_biUnion.mpr
  exact ⟨i, Finset.mem_univ _, Finset.mem_map.mpr ⟨p,hp,rfl⟩⟩

theorem source_primitiveLabel_coordinates (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (l : c.Labels w) :
    coordinates ((inventory w hw v).source (primitiveLabel w hw v i c he l)) =
      shiftPoint (tileStride w*((codes w v).get i).1.1) (tileStride w*((codes w v).get i).1.2)
        (c.actor w hw false l) := by
  rw [source_primitiveLabel]
  subst c
  simp only [primitiveEmbedding, inventory, InventoryAssembly.embedding, GridEmbedding.translate, coordinates,
    PrimitiveCode.actor, PrimitiveCode.world, shiftPoint, Nat.add_assoc, Bool.false_eq_true, ite_false]
  rfl

theorem target_primitiveLabel_coordinates (i : Fin (codes w v).length) (c : PrimitiveCode)
    (he : ((codes w v).get i).2 = c) (l : c.Labels w) :
    coordinates ((inventory w hw v).target (primitiveLabel w hw v i c he l)) =
      shiftPoint (tileStride w*((codes w v).get i).1.1) (tileStride w*((codes w v).get i).1.2)
        (c.actor w hw true l) := by
  rw [target_primitiveLabel]
  subst c
  simp only [primitiveEmbedding, inventory, InventoryAssembly.embedding, GridEmbedding.translate, coordinates,
    PrimitiveCode.actor, PrimitiveCode.world, shiftPoint, Nat.add_assoc, ite_true]
  rfl

end PushPuzzle.PushS.FiniteSourceInventory

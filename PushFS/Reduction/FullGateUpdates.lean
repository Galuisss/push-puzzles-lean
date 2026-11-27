/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateSelectedSlots

/-! Advancing one real primitive retains the exact foreign inventory and selects its prescribed target phase. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open scoped Classical
set_option maxRecDepth 65536
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

noncomputable def advance (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) :
    Inventory.Index g→Bool := Function.update f i true

theorem advance_self (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) :
    advance g f i i=true := Function.update_self _ _ _

private theorem profileMask_advance (g : GateTileState) (f : Inventory.Index g→Bool)
    (i : Inventory.Index g) :
    profileMask g (advance g f i)=Function.update (profileMask g f) ((Inventory.numbering g) i) true := by
  funext j
  by_cases hj : j=(Inventory.numbering g) i
  · subst j
    simp only [profileMask_at,advance_self,Function.update_self]
  · have hk : (Inventory.numbering g).symm j≠i := by
      intro he
      apply hj
      have hh:=congrArg (Inventory.numbering g) he
      exact (Equiv.apply_symm_apply _ _).symm.trans hh
    simp only [profileMask,advance,Function.update_of_ne hk,Function.update_of_ne hj]

theorem profileOutside_advance (g : GateTileState) (f : Inventory.Index g→Bool) (i : Inventory.Index g) :
    @Eq (Finset C) (profileOutside g (advance g f i) i) (profileOutside g f i) := by
  unfold profileOutside
  rw [profileMask_advance,(fullAtlas g).profileOutside_update]

theorem armPhase_source (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) (i : Inventory.Index g)
    (hi : f i=false) : armPhase g f r i=Inventory.initialPhase g r := by
  simp only [armPhase,hi,Bool.false_eq_true,ite_false]

theorem armPhase_target (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) (i : Inventory.Index g)
    (hi : f i=true) : armPhase g f r i=Inventory.targetPhase g r := by
  simp only [armPhase,hi,ite_true]

theorem armPhase_advance_self (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) (i : Inventory.Index g) :
    armPhase g (advance g f i) r i=Inventory.targetPhase g r := by
  simp only [armPhase,advance_self,ite_true]

end PushPuzzle.PushFS.Reduction.GateTileRouting

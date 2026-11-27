/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateLineMacros
public import PushFS.Reduction.FullGateCornerMacros

/-! The actual alternating long-line/short-corner order along a complete gate arm. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] profile profileOutside cornerKind cornerOrientation

def armCount (g : GateTileState) (r : Fin 3) : ℕ := 2*(curve (key g r)).length-1

def armLineNode (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) : Fin (armCount g r) :=
  ⟨2*j.val,by have hj:=j.isLt; change 2*j.val<2*(curve (key g r)).length-1; omega⟩

def armCornerNode (g : GateTileState) (r : Fin 3) (k : Fin ((curve (key g r)).length-1)) : Fin (armCount g r) :=
  ⟨2*k.val+1,by have hk:=k.isLt; change 2*k.val+1<2*(curve (key g r)).length-1; omega⟩

def armNodeLineIndex (g : GateTileState) (r : Fin 3) (i : Fin (armCount g r)) : Fin (curve (key g r)).length :=
  ⟨i.val/2,by have hi : i.val<2*(curve (key g r)).length-1:=i.isLt; omega⟩

def armNodeCornerIndex (g : GateTileState) (r : Fin 3) (i : Fin (armCount g r)) (hi : i.val%2≠0) :
    Fin ((curve (key g r)).length-1) :=
  ⟨i.val/2,by have hb : i.val<2*(curve (key g r)).length-1:=i.isLt; omega⟩

def armNode (g : GateTileState) (r : Fin 3) (i : Fin (armCount g r)) : Inventory.Index g :=
  if hi : i.val%2=0 then lineIndex g r (armNodeLineIndex g r i)
  else cornerIndex g r (armNodeCornerIndex g r i hi)

theorem armNode_line (g : GateTileState) (r : Fin 3) (j : Fin (curve (key g r)).length) :
    armNode g r (armLineNode g r j)=lineIndex g r j := by
  have he : (armLineNode g r j).val%2=0 := by change (2*j.val)%2=0; omega
  rw [armNode,dite_eq_left he]
  apply congrArg (lineIndex g r)
  apply Fin.ext
  change 2*j.val/2=j.val
  omega

theorem armNode_corner (g : GateTileState) (r : Fin 3) (k : Fin ((curve (key g r)).length-1)) :
    armNode g r (armCornerNode g r k)=cornerIndex g r k := by
  have he : (armCornerNode g r k).val%2≠0 := by change (2*k.val+1)%2≠0; omega
  rw [armNode,dite_eq_right he]
  apply congrArg (cornerIndex g r)
  apply Fin.ext
  change (2*k.val+1)/2=k.val
  omega

private def armPosition (g : GateTileState) : Inventory.Index g→ℕ
  | .inr (.inl ⟨_,.inl j⟩)=>2*j.val
  | .inr (.inl ⟨_,.inr k⟩)=>2*k.val+1
  | _=>0

private theorem armPosition_node (g : GateTileState) (r : Fin 3) (i : Fin (armCount g r)) :
    armPosition g (armNode g r i)=i.val := by
  unfold armNode
  split_ifs with he
  · change 2*(i.val/2)=i.val
    omega
  · change 2*(i.val/2)+1=i.val
    omega

theorem armNode_injective (g : GateTileState) (r : Fin 3) : Function.Injective (armNode g r) := by
  intro i j he
  apply Fin.ext
  exact (armPosition_node g r i).symm.trans ((congrArg (armPosition g) he).trans (armPosition_node g r j))

structure ArmFrontier (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3) (i : Fin (armCount g r)) : Prop where
  fresh : f (armNode g r i)=false
  before : ∀j : Fin (armCount g r),j.val < i.val →armPhase g f r (armNode g r j)=false
  after : ∀j : Fin (armCount g r),i.val < j.val →armPhase g f r (armNode g r j)=true
  buffer : armPhase g f r (.inl (frontierBufferIndex r))=false

end PushPuzzle.PushFS.Reduction.GateTileRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateArmOrder
public import PushFS.Reduction.ProfileSweep
public import Mathlib.Data.Fin.Rev

/-! Complete physical propagation along the alternating native primitives of either gate-arm phase change. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] profile profileOutside cornerKind cornerOrientation

private theorem armNode_ne_buffer (g : GateTileState) (r : Fin 3) (j : Fin (armCount g r)) (b : Fin 4) :
    armNode g r j≠.inl b := by
  unfold armNode
  split_ifs <;> (intro he; cases he)

noncomputable def commitArm (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3) :
    Inventory.Index g→Bool := ProfileSweep.stage (armNode g r) base (armCount g r)

theorem commitArm_line (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3)
    (j : Fin (curve (key g r)).length) : commitArm g base r (lineIndex g r j)=true := by
  have h:=ProfileSweep.node_true (armNode g r) base (armCount g r) (armLineNode g r j) (armLineNode g r j).isLt
  rwa [armNode_line] at h

theorem commitArm_corner (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) : commitArm g base r (cornerIndex g r k)=true := by
  have h:=ProfileSweep.node_true (armNode g r) base (armCount g r) (armCornerNode g r k) (armCornerNode g r k).isLt
  rwa [armNode_corner] at h

theorem commitArm_buffer (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3) (b : Fin 4) :
    commitArm g base r (.inl b)=base (.inl b) :=
  ProfileSweep.outside _ _ _ _ (fun j=>armNode_ne_buffer g r j b)

theorem down_frontier (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3)
    (hbase : ∀j,base (armNode g r j)=false)
    (ha : Inventory.initialPhase g r=true) (hb : Inventory.targetPhase g r=false)
    (hbuffer : armPhase g base r (.inl (frontierBufferIndex r))=false) (i : Fin (armCount g r)) :
    ArmFrontier g (ProfileSweep.stage (armNode g r) base i.val) r i := by
  refine ⟨ProfileSweep.node_false _ (armNode_injective g r) base hbase _ i (le_refl _),?_,?_,?_⟩
  · intro j hj
    exact (armPhase_target _ _ _ _ (ProfileSweep.node_true _ base _ j hj)).trans hb
  · intro j hj
    exact (armPhase_source _ _ _ _ (ProfileSweep.node_false _ (armNode_injective g r) base hbase _ j (by omega))).trans ha
  · have he:=ProfileSweep.outside (armNode g r) base i.val (.inl (frontierBufferIndex r))
      (fun j=>armNode_ne_buffer g r j _)
    simpa only [armPhase,he] using hbuffer

theorem reverse_finish {α : Type} {n : ℕ} (node : Fin n→α) (base : α→Bool) :
    ProfileSweep.stage (fun j=>node j.rev) base n=ProfileSweep.stage node base n := by
  funext i
  apply ite_cond_congr
  apply propext
  constructor
  · rintro ⟨j,_,he⟩
    exact ⟨j.rev,j.rev.isLt,he⟩
  · rintro ⟨j,_,he⟩
    exact ⟨j.rev,j.rev.isLt,by simpa only [Fin.rev_rev] using he⟩

theorem up_frontier (g : GateTileState) (base : Inventory.Index g→Bool) (r : Fin 3)
    (hbase : ∀j,base (armNode g r j)=false)
    (ha : Inventory.initialPhase g r=false) (hb : Inventory.targetPhase g r=true)
    (hbuffer : armPhase g base r (.inl (frontierBufferIndex r))=false) (i : Fin (armCount g r)) :
    ArmFrontier g (ProfileSweep.stage (fun j=>armNode g r j.rev) base i.val) r i.rev := by
  have hinj : Function.Injective (fun j : Fin (armCount g r)=>armNode g r j.rev):=
    (armNode_injective g r).comp Fin.rev_injective
  have hf : ∀j : Fin (armCount g r),base (armNode g r j.rev)=false:=fun j=>hbase j.rev
  refine ⟨ProfileSweep.node_false _ hinj base hf _ i (le_refl _),?_,?_,?_⟩
  · intro j hj
    have he : ProfileSweep.stage (fun k=>armNode g r k.rev) base i.val (armNode g r j)=false:=by
      have h:=ProfileSweep.node_false (fun k=>armNode g r k.rev) hinj base hf i.val j.rev (by
        have h:=Fin.rev_lt_rev.mpr hj
        simpa only [Fin.rev_rev] using Nat.le_of_lt h)
      simpa only [Fin.rev_rev] using h
    exact (armPhase_source _ _ _ _ he).trans ha
  · intro j hj
    have he : ProfileSweep.stage (fun k=>armNode g r k.rev) base i.val (armNode g r j)=true:=by
      have hh : j.rev.val < i.val:=by
        have h:=Fin.rev_lt_rev.mpr hj
        simpa only [Fin.rev_rev,Fin.lt_def] using h
      have h:=ProfileSweep.node_true (fun k=>armNode g r k.rev) base i.val j.rev hh
      simpa only [Fin.rev_rev] using h
    exact (armPhase_target _ _ _ _ he).trans hb
  · have he:=ProfileSweep.outside (fun j=>armNode g r j.rev) base i.val (.inl (frontierBufferIndex r))
      (fun j=>armNode_ne_buffer g r j.rev _)
    simpa only [armPhase,he] using hbuffer

end PushPuzzle.PushFS.Reduction.GateTileRouting

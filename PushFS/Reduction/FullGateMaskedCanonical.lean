/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateCanonical
public import PushFS.Reduction.FullGateMaskedMacros

/-! Canonical full-gate Push-1FS macros retain the exact real exterior endpoint inventory. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profile profileOutside selectedMarks cornerKind cornerOrientation annularProfileBoxes annularBoxes

private theorem masked_arm_update_at_frontier (g : GateTileState) (f : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (ready : ExternalReady g fixed r)
    (i : Fin (armCount g r)) (frontier : ArmFrontier g f r i) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g f fixed (fullAtlas g).player)
      (maskedProfile g (advance g f (armNode g r i)) fixed (fullAtlas g).player) := by
  by_cases he : i.val%2=0
  · let j:=armNodeLineIndex g r i
    have hnode : armNode g r i=lineIndex g r j := dite_eq_left he
    have hval : i.val=2*j.val := by change i.val=2*(i.val/2); omega
    have fresh:=frontier.fresh
    rw [hnode] at fresh ⊢
    apply masked_line_update g f fixed hm r ready j fresh
    refine ⟨fun _=>frontier.buffer,?_,?_⟩
    · intro k hk
      have hp:=frontier.before (armCornerNode g r k) (by change 2*k.val+1 < i.val; omega)
      rwa [armNode_corner] at hp
    · intro k hk
      have hp:=frontier.after (armCornerNode g r k) (by change i.val<2*k.val+1; omega)
      rwa [armNode_corner] at hp
  · let k:=armNodeCornerIndex g r i he
    have hnode : armNode g r i=cornerIndex g r k := dite_eq_right he
    have hval : i.val=2*k.val+1 := by change i.val=2*(i.val/2)+1; omega
    have fresh:=frontier.fresh
    rw [hnode] at fresh ⊢
    apply masked_corner_update g f fixed hm r k fresh
    constructor
    · have hp:=frontier.before (armLineNode g r (cornerInLine g r k)) (by change 2*k.val < i.val; omega)
      rwa [armNode_line] at hp
    · have hp:=frontier.after (armLineNode g r (cornerOutLine g r k)) (by change i.val<2*(k.val+1); omega)
      rwa [armNode_line] at hp

private theorem masked_armSweep_down (g : GateTileState) (base : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (ready : ExternalReady g fixed r)
    (hbase : ∀j,base (armNode g r j)=false)
    (ha : Inventory.initialPhase g r=true) (hb : Inventory.targetPhase g r=false)
    (hbuffer : armPhase g base r (.inl (frontierBufferIndex r))=false) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g base fixed (fullAtlas g).player)
      (maskedProfile g (commitArm g base r) fixed (fullAtlas g).player) := by
  apply ProfileSweep.replay (armNode g r) base (fun f=>maskedProfile g f fixed (fullAtlas g).player)
  intro j
  have hh:=masked_arm_update_at_frontier g _ fixed hm r ready j (down_frontier g base r hbase ha hb hbuffer j)
  have he : advance g (ProfileSweep.stage (armNode g r) base j.val) (armNode g r j)=
      ProfileSweep.stage (armNode g r) base (j.val+1):=by
    unfold advance
    exact ProfileSweep.step _ _ j
  rwa [he] at hh

private theorem masked_armSweep_up (g : GateTileState) (base : Inventory.Index g→Bool)
    (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p) (r : Fin 3) (ready : ExternalReady g fixed r)
    (hbase : ∀j,base (armNode g r j)=false)
    (ha : Inventory.initialPhase g r=false) (hb : Inventory.targetPhase g r=true)
    (hbuffer : armPhase g base r (.inl (frontierBufferIndex r))=false) :
    Reachable (fullPuzzle g).board (some 1) (maskedProfile g base fixed (fullAtlas g).player)
      (maskedProfile g (commitArm g base r) fixed (fullAtlas g).player) := by
  have hh:=ProfileSweep.replay (fun j : Fin (armCount g r)=>armNode g r j.rev) base
    (fun f=>maskedProfile g f fixed (fullAtlas g).player) (fullPuzzle g).board (fun j=>by
      have hh:=masked_arm_update_at_frontier g _ fixed hm r ready j.rev (up_frontier g base r hbase ha hb hbuffer j)
      have he : advance g (ProfileSweep.stage (fun k=>armNode g r k.rev) base j.val) (armNode g r j.rev)=
          ProfileSweep.stage (fun k=>armNode g r k.rev) base (j.val+1):=by
        unfold advance
        exact ProfileSweep.step _ _ j
      rwa [he] at hh)
  rw [reverse_finish] at hh
  exact hh

private theorem masked_profile_initial (g : GateTileState) (fixed : Finset C) :
    maskedProfile g (fun _=>false) fixed (fullAtlas g).player=Gates.withFixed (w:=200007) (h:=198068) fixed (fullPuzzle g).initial := by
  have hh:=profile_initial g
  apply State.ext
  · change (fullAtlas g).player=(fullPuzzle g).initial.player
    have hp:=congrArg State.player hh
    unfold profile StorageAtlas.profileAt at hp
    exact hp
  · exact congrArg (fun s=>s.boxes∪fixed) hh

private theorem masked_profile_finished (g : GateTileState) (f : Inventory.Index g→Bool) (fixed : Finset C)
    (hs : Gates.singleChange g.core.initial g.core.target)
    (hf : ∀i : Fin 4,f (.inl i)=true)
    (hl : ∀j,f (lineIndex g (Gates.changingPort g.core.initial g.core.target) j)=true)
    (hc : ∀j,f (cornerIndex g (Gates.changingPort g.core.initial g.core.target) j)=true) :
    maskedProfile g f fixed (fullAtlas g).player=Gates.withFixed (w:=200007) (h:=198068) fixed ⟨(fullAtlas g).player,(fullPuzzle g).board.goals⟩ := by
  apply State.ext
  · rfl
  · exact congrArg (fun s=>s.boxes∪fixed) (profile_finished g f hs hf hl hc (fullAtlas g).player)

/-- Every real exterior box is retained by the full canonical single-port gate macro. -/
theorem masked_full_transition (g : GateTileState) (fixed : Finset C)
    (hm : ∀p∈fixed,OuterMask g p)
    (ready : ExternalReady g fixed (Gates.changingPort g.core.initial g.core.target))
    (ha : Gates.legal g.core.isAND g.core.initial) (hb : Gates.legal g.core.isAND g.core.target)
    (hs : Gates.singleChange g.core.initial g.core.target) :
    Reachable (fullPuzzle g).board (some 1) (Gates.withFixed (w:=200007) (h:=198068) fixed (fullPuzzle g).initial)
      (Gates.withFixed (w:=200007) (h:=198068) fixed ⟨(fullAtlas g).player,(fullPuzzle g).board.goals⟩) := by
  let r:=Gates.changingPort g.core.initial g.core.target
  have hne : Inventory.initialPhase g r≠Inventory.targetPhase g r:=(changed_claims _ _ hs).1
  rw [←masked_profile_initial g fixed]
  cases hphase : Inventory.initialPhase g r
  · have ht : Inventory.targetPhase g r=true:=by cases hb' : Inventory.targetPhase g r <;> simp_all
    have hu:=masked_armSweep_up g (fun _=>false) fixed hm r ready (fun _=>rfl) hphase ht
      (armPhase_source _ _ _ _ rfl |>.trans hphase)
    have hh:=masked_buffer_transition g (commitArm g (fun _=>false) r) fixed hm
      (fun i=>commitArm_buffer g _ r i) ha hb hs (by
        exact (armPhase_target _ _ _ _ (commitArm_line g _ r (firstLineIndex g r))).trans ht)
    have he:=masked_profile_finished g (commitBuffer g (commitArm g (fun _=>false) r)) fixed hs
      (fun _=>rfl) (fun j=>commitArm_line g _ r j) (fun j=>commitArm_corner g _ r j)
    exact hu.trans (he ▸hh)
  · have ht : Inventory.targetPhase g r=false:=by cases hb' : Inventory.targetPhase g r <;> simp_all
    have hh:=masked_buffer_transition g (fun _=>false) fixed hm (fun _=>rfl) ha hb hs
      ((armPhase_source _ _ _ _ rfl).trans hphase)
    have hd:=masked_armSweep_down g (commitBuffer g (fun _=>false)) fixed hm r ready
      (commitBuffer_arm_fresh g r) hphase ht ((armPhase_target _ _ _ _ rfl).trans ht)
    have he:=masked_profile_finished g (commitArm g (commitBuffer g (fun _=>false)) r) fixed hs
      (fun i=>commitArm_buffer g _ r i) (commitArm_line g _ r) (commitArm_corner g _ r)
    exact hh.trans (he ▸hd)

end PushPuzzle.PushFS.Reduction.GateTileRouting

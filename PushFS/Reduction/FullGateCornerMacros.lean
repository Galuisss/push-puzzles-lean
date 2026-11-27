/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateFrontierWalking
public import PushFS.Reduction.FullGateSeamGeometry
public import PushFS.Reduction.FullGateLineWalking
public import PushFS.Reduction.FullGateCornerWalking
public import PushFS.Reduction.FullGateUpdates

/-! Complete real protected-corner updates retain every foreign primitive and the common actual player. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes profile profileOutside selectedMarks cornerKind cornerOrientation

structure CornerPrepared (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) : Prop where
  incoming : armPhase g f r (lineIndex g r (cornerInLine g r k))=false
  outgoing : armPhase g f r (lineIndex g r (cornerOutLine g r k))=true

theorem corner_macro_collar (g : GateTileState) (f : Inventory.Index g→Bool) (r : Fin 3)
    (k : Fin ((curve (key g r)).length-1)) (prepared : CornerPrepared g f r k) :
    Polyline.Frame.fixed (armCornerEmbedding g r k) (profileOutside g f (cornerIndex g r k))⊆
      (ShortCorners.template (cornerKind (key g r) k.val)).neighbors := by
  intro p hp
  obtain ⟨j,hj,q,hq,he⟩:=corner_foreign_line g f r k p ((Polyline.Frame.mem_fixed _ _ p).mp hp)
  obtain ⟨l,hl⟩:=selected_line_coordinates g f r j q hq
  have he':=congrArg (fun p : C=>(p.1.val,p.2.val)) he
  have hs:=hl.symm.trans (he'.trans (arm_corner_coordinates g r k p))
  clear hp he he' hl hq q
  rcases hj with hj|hj
  · have hphase : armPhase g f r (lineIndex g r j)=false :=
      (congrArg (fun i=>armPhase g f r (lineIndex g r i)) (show j=cornerInLine g r k from Fin.ext hj)).trans prepared.incoming
    rw [hphase] at hs
    exact near_selected_line_macro (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
      (Inventory.targetPhase g r) l p hs
  · have hphase : armPhase g f r (lineIndex g r j)=true :=
      (congrArg (fun i=>armPhase g f r (lineIndex g r i)) (show j=cornerOutLine g r k from Fin.ext hj)).trans prepared.outgoing
    rw [hphase] at hs
    exact far_selected_line_macro (key g r) j.val k.val hj j.isLt (cornerOutLine g r k).isLt
      (Inventory.targetPhase g r) l p hs

end PushPuzzle.PushFS.Reduction.GateTileRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.PhysicalEdgeFrontier

/-! Compose the actual finite frontier updates into a complete physical source-edge traversal. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires SourceCanonical
open scoped Classical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

theorem edge_replay (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount)
    (hupdate : ∀(f : Fin (Fintype.card (Index (edgeSource w c e)))→Bool) (i : Index (edgeSource w c e)),
      EdgeFrontier (edgeSource w c e) e.val f i→Reachable (atlas (edgeSource w c e) hP hT).board (some 1)
        ((atlas (edgeSource w c e) hP hT).profileAt f (atlas (edgeSource w c e) hP hT).player)
        ((atlas (edgeSource w c e) hP hT).profileAt (Function.update f (numbering (edgeSource w c e) i) true)
          (atlas (edgeSource w c e) hP hT).player)) :
    Reachable (atlas (edgeSource w c e) hP hT).board (some 1)
      ((atlas (edgeSource w c e) hP hT).profileAt (fun _=>false) (atlas (edgeSource w c e) hP hT).player)
      ((atlas (edgeSource w c e) hP hT).profileAt (fun _=>true) (atlas (edgeSource w c e) hP hT).player) := by
  let v:=edgeSource w c e
  let A:=atlas v hP hT
  obtain ⟨order⟩:=edgeOrder_exists v hP hT e
  have hflip : edgePhase v e.val true= !(edgePhase v e.val false):=by
    have hh:=wire_phase_reverse c e e
    simpa only [v,edgePhase,edgeSource,PhysicalTiles.bits,Bool.false_eq_true,ite_false,ite_true] using hh
  cases ha : edgePhase v e.val false
  · have hb : edgePhase v e.val true=true:=by rw [ha] at hflip; exact hflip
    have hr:=ProfileSweep.replay (fun j : Fin (order.sequence.length+1)=>order.numberedNode hP hT j.rev)
      (fun _=>false) (fun f=>A.profileAt f A.player) A.board (fun j=>by
        have hh:=hupdate _ _ (order.backward_frontier hP hT ha hb j)
        have he:=ProfileSweep.step (fun k : Fin (order.sequence.length+1)=>order.numberedNode hP hT k.rev) (fun _=>false) j
        change Function.update (order.backwardMask hP hT j.val) (order.numberedNode hP hT j.rev) true=
          ProfileSweep.stage (fun k : Fin (order.sequence.length+1)=>order.numberedNode hP hT k.rev) (fun _=>false) (j.val+1) at he
        change Reachable A.board (some 1) (A.profileAt (order.backwardMask hP hT j.val) A.player)
          (A.profileAt (Function.update (order.backwardMask hP hT j.val) (order.numberedNode hP hT j.rev) true) A.player) at hh
        rw [he] at hh
        simpa only [EdgeOrder.backwardMask] using hh)
    have hf:=edge_profile_finished w hw hP hT c e
      (ProfileSweep.stage (fun k : Fin (order.sequence.length+1)=>order.numberedNode hP hT k.rev) (fun _=>false) (order.sequence.length+1))
      (fun i hp=>by
        obtain ⟨j,hj⟩:=order.covers hP hT i hp
        rw [←hj]
        have hh:=ProfileSweep.node_true (fun k : Fin (order.sequence.length+1)=>order.numberedNode hP hT k.rev)
          (fun _=>false) (order.sequence.length+1) j.rev j.rev.isLt
        simpa only [Fin.rev_rev,EdgeOrder.numberedNode] using hh)
    have he : A.profileAt (ProfileSweep.stage (fun k : Fin (order.sequence.length+1)=>order.numberedNode hP hT k.rev)
        (fun _=>false) (order.sequence.length+1)) A.player=A.profileAt (fun _=>true) A.player:=by
      apply State.ext
      · rfl
      · exact hf.trans A.profile_target.symm
    exact he ▸hr
  · have hb : edgePhase v e.val true=false:=by rw [ha] at hflip; exact hflip
    have hr:=ProfileSweep.replay (order.numberedNode hP hT) (fun _=>false) (fun f=>A.profileAt f A.player) A.board (fun j=>by
      have hh:=hupdate _ _ (order.forward_frontier hP hT ha hb j)
      have he:=ProfileSweep.step (order.numberedNode hP hT) (fun _=>false) j
      change Function.update (order.forwardMask hP hT j.val) (order.numberedNode hP hT j) true=
        ProfileSweep.stage (order.numberedNode hP hT) (fun _=>false) (j.val+1) at he
      change Reachable A.board (some 1) (A.profileAt (order.forwardMask hP hT j.val) A.player)
        (A.profileAt (Function.update (order.forwardMask hP hT j.val) (order.numberedNode hP hT j) true) A.player) at hh
      rw [he] at hh
      simpa only [EdgeOrder.forwardMask] using hh)
    have hf:=edge_profile_finished w hw hP hT c e
      (ProfileSweep.stage (order.numberedNode hP hT) (fun _=>false) (order.sequence.length+1)) (fun i hp=>by
        obtain ⟨j,hj⟩:=order.covers hP hT i hp
        rw [←hj]
        exact ProfileSweep.node_true _ _ _ j j.isLt)
    have he : A.profileAt (ProfileSweep.stage (order.numberedNode hP hT) (fun _=>false) (order.sequence.length+1)) A.player=
        A.profileAt (fun _=>true) A.player:=by
      apply State.ext
      · rfl
      · exact hf.trans A.profile_target.symm
    exact he ▸hr

end PushPuzzle.PushFS.Reduction.PhysicalInventory

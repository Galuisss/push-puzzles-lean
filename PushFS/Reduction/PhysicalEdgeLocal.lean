/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module
public import PushFS.Reduction.PhysicalEdgeFrontier
public import PushFS.Reduction.PhysicalGateMacros
public import PushFS.Reduction.PhysicalWirePreparedFrame

/-! Every actual edge-frontier tile has its complete whole-board Push-1FS update at its real player hub. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires SourceCanonical
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board StorageAtlas.profileBoxes

private theorem profile_idle_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v)
    (p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hi : (PhysicalTiles.piece (tile i)).initial.boxes=(PhysicalTiles.piece (tile i)).board.goals) :
    (atlas v hP hT).profileAt f p=(atlas v hP hT).profileAt (Function.update f (numbering v i) true) p := by
  apply StorageAtlas.profile_update_of_diagonal
  change (PhysicalTiles.piece (tile ((numbering v).symm (numbering v i)))).initial.boxes=
    (PhysicalTiles.piece (tile ((numbering v).symm (numbering v i)))).board.goals
  rw [Equiv.symm_apply_apply]
  exact hi

private theorem wire_update_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v) (a : Catalog.Bitmap.Args) (htile : tile i=.inr a)
    (hi : f (numbering v i)=false) (prepared : WirePrepared v f i.val.1 a) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player))
      ((atlas v hP hT).profileAt (Function.update f (numbering v i) true)
        ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player)) := by
  rcases i with ⟨⟨p,k⟩,hk⟩
  change k=.inr a at htile
  subst k
  exact wire_update v hP hT f p a hk hi prepared

private theorem edge_gate_update_at (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount)
    (hc : (Word.compile w).graph.Legal c) (hd : (Word.compile w).graph.Legal (reverse c e))
    (f : Fin (Fintype.card (Index (edgeSource w c e)))→Bool) (i : Index (edgeSource w c e))
    (a : GateTileState) (htile : tile i=.inl a)
    (frontier : EdgeFrontier (edgeSource w c e) e.val f i) :
    Reachable (atlas (edgeSource w c e) hP hT).board (some 1)
      ((atlas (edgeSource w c e) hP hT).profileAt f
        ((embedding (edgeSource w c e) i).cells (PhysicalTiles.piece (tile i)).initial.player))
      ((atlas (edgeSource w c e) hP hT).profileAt (Function.update f (numbering (edgeSource w c e) i) true)
        ((embedding (edgeSource w c e) i).cells (PhysicalTiles.piece (tile i)).initial.player)) := by
  let v:=edgeSource w c e
  obtain ⟨g,hg,ha,hpos⟩:=gate_record v i a htile
  have hi : i=gateIndex v g hg:=position_injective (hpos.trans (gateIndex_position v g hg).symm)
  subst i
  subst a
  have hstep : (Word.compile w).graph.Step c (reverse c e):=⟨hc,hd,e,rfl⟩
  obtain ⟨hlegalA,hlegalB,he|hs⟩:=step_gates w hw hP hT hstep g hg
  · have hdiag : (PhysicalTiles.piece (tile (gateIndex v g hg))).initial.boxes=
        (PhysicalTiles.piece (tile (gateIndex v g hg))).board.goals:=gate_diagonal _ he
    have hh:=profile_idle_index v hP hT f (gateIndex v g hg)
        ((embedding v (gateIndex v g hg)).cells (PhysicalTiles.piece (tile (gateIndex v g hg))).initial.player) hdiag
    rw [←hh]
  · have he:=changingPort_edge w hw hP hT c e g hg hs
    have hr:=frontier.gate_released hP hT g hg rfl _ he
    have hh:=gate_update_at v hP hT f g hg frontier.fresh hr hlegalA hlegalB hs
    have hplayer : (PhysicalTiles.piece (tile (gateIndex v g hg))).initial.player=
        (GateTileRouting.fullAtlas (gateTileState (g,v.2))).player:=by
      have hp:=congrArg State.player (GateTileRouting.profile_initial (gateTileState (g,v.2)))
      unfold GateTileRouting.profile StorageAtlas.profileAt at hp
      exact hp.symm
    rw [hplayer]
    exact hh


/-- One tile of the actual finite source-edge traversal changes every owned box and keeps every foreign box. -/
theorem edge_tile_update_at (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin w.compile.edgeCount→Bool) (e : Fin w.compile.edgeCount)
    (hc : (Word.compile w).graph.Legal c) (hd : (Word.compile w).graph.Legal (reverse c e))
    (f : Fin (Fintype.card (Index (edgeSource w c e)))→Bool) (i : Index (edgeSource w c e))
    (frontier : EdgeFrontier (edgeSource w c e) e.val f i) :
    Reachable (atlas (edgeSource w c e) hP hT).board (some 1)
      ((atlas (edgeSource w c e) hP hT).profileAt f
        ((embedding (edgeSource w c e) i).cells (PhysicalTiles.piece (tile i)).initial.player))
      ((atlas (edgeSource w c e) hP hT).profileAt (Function.update f (numbering (edgeSource w c e) i) true)
        ((embedding (edgeSource w c e) i).cells (PhysicalTiles.piece (tile i)).initial.player)) := by
  let v:=edgeSource w c e
  rcases i with ⟨⟨p,k⟩,hkey⟩
  cases k with
  | inr a=>
    exact wire_update_index v hP hT f ⟨(p,.inr a),hkey⟩ a rfl frontier.fresh
      (frontier.wire_prepared hP hT p a rfl rfl)
  | inl a=>exact edge_gate_update_at w hw hP hT c e hc hd f ⟨(p,.inl a),hkey⟩ a rfl frontier

end PushPuzzle.PushFS.Reduction.PhysicalInventory

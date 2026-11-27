/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGatePrepared
public import PushFS.Reduction.PhysicalWireMacros
public import PushFS.Reduction.FullGateMaskedCanonical

/-! A prepared actual source gate updates its entire physical inventory while retaining every foreign box. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes gateProfileFixed

/-- The real source neighbor's selected phase instantiates the full gate macro's literal strict external collar. -/
private theorem gate_external_ready (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1)
    (role : Fin 3) (released : GatePortReleased v f g role) :
    ExternalReady (gateTileState (g,v.2)) (gateProfileFixed v hP hT f g hg) role :=
  gate_profile_released_collar v hP hT f g hg role released

/-- A legal single-port actual gate macro changes every real core, lead, annular line and protected-turn inventory and returns its actual player. -/
theorem gate_update_at (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1)
    (hi : f (numbering v (gateIndex v g hg))=false)
    (released : GatePortReleased v f g (Gates.changingPort (gateTileState (g,v.2)).core.initial (gateTileState (g,v.2)).core.target))
    (ha : Gates.legal (gateTileState (g,v.2)).core.isAND (gateTileState (g,v.2)).core.initial)
    (hb : Gates.legal (gateTileState (g,v.2)).core.isAND (gateTileState (g,v.2)).core.target)
    (hs : Gates.singleChange (gateTileState (g,v.2)).core.initial (gateTileState (g,v.2)).core.target) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells (fullAtlas (gateTileState (g,v.2))).player))
      ((atlas v hP hT).profileAt (Function.update f (numbering v (gateIndex v g hg)) true)
        ((gateEmbedding v g hg).cells (fullAtlas (gateTileState (g,v.2))).player)) := by
  have hlocal:=masked_full_transition (gateTileState (g,v.2)) (gateProfileFixed v hP hT f g hg)
    (gate_profile_fixed_mask v hP hT f g hg) (gate_external_ready v hP hT f g hg _ released) ha hb hs
  have hr:=(gateEmbedding v g hg).reachable_withFixed (gate_walls_agree v hP hT g hg)
    (fun p hp=>(mem_gateProfileFixed v hP hT f g hg p).mpr hp)
    (fun p hp=>(mem_gateProfileFixed v hP hT f g hg p).mp hp)
    ((atlas v hP hT).profileOutside_floor f (numbering v (gateIndex v g hg))) hlocal
  have hstart:=profile_place_source_index v hP hT f (gateIndex v g hg) hi
  have hend:=profile_place_target_index v hP hT f (gateIndex v g hg)
  have hplayer : (PhysicalTiles.piece (tile (gateIndex v g hg))).initial.player=(fullAtlas (gateTileState (g,v.2))).player:=by
    have he:=congrArg State.player (profile_initial (gateTileState (g,v.2)))
    unfold profile StorageAtlas.profileAt at he
    exact he.symm
  rw [hplayer] at hstart hend
  exact Eq.mp (congrArg₂ (Reachable (atlas v hP hT).board (some 1)) hstart hend) hr

end PushPuzzle.PushFS.Reduction.PhysicalInventory

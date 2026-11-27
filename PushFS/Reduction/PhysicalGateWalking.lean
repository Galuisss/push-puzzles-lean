/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateForeign
public import PushFS.Reduction.PhysicalProfilePlacements
public import PushFS.Reduction.FullGateMaskedConnected

/-! Actual full-gate player access on the complete mixed physical board. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes gateProfileFixed profile maskedProfile

private theorem uniform_profile_boxes (g : GateTileState) (b : Bool) :
    (profile g (fun _=>b) (fullAtlas g).player).boxes=PhysicalTiles.marks b (.inl g) := by
  cases b
  · exact congrArg State.boxes (profile_initial g)
  · exact profile_target g (fullAtlas g).player

/-- A genuine fixed-neighbor local full-gate walk is a genuine walk of the entire physical mixed inventory. -/
private theorem gate_profile_walk (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1)
    (p q : GateTileRouting.C)
    (hr : Reachable (fullPuzzle (gateTileState (g,v.2))).board (some 1)
      (maskedProfile (gateTileState (g,v.2)) (fun _=>f (numbering v (gateIndex v g hg)))
        (gateProfileFixed v hP hT f g hg) p)
      (maskedProfile (gateTileState (g,v.2)) (fun _=>f (numbering v (gateIndex v g hg)))
        (gateProfileFixed v hP hT f g hg) q)) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells p))
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells q)) := by
  let s:=gateTileState (g,v.2)
  let i:=gateIndex v g hg
  let phase:=f (numbering v i)
  let fixed:=gateProfileFixed v hP hT f g hg
  let atPoint (p : GateTileRouting.C) : State 200007 198068:=⟨p,PhysicalTiles.marks phase (.inl s)⟩
  have he (p : GateTileRouting.C) : maskedProfile s (fun _=>phase) fixed p=Gadgets.Gates.withFixed fixed (atPoint p) := by
    unfold maskedProfile
    apply State.ext
    · rfl
    · exact congrArg (fun xs=>xs∪fixed) (uniform_profile_boxes s phase)
  have hr':=Eq.mp (congrArg₂ (Reachable (fullPuzzle s).board (some 1)) (he p) (he q)) hr
  have hh:=(gateEmbedding v g hg).reachable_withFixed (gate_walls_agree v hP hT g hg)
    (fun p hp=>(mem_gateProfileFixed v hP hT f g hg p).mpr hp)
    (fun p hp=>(mem_gateProfileFixed v hP hT f g hg p).mp hp)
    ((atlas v hP hT).profileOutside_floor f (numbering v i)) hr'
  have hp:=profile_place_index v hP hT f i p
  have hq:=profile_place_index v hP hT f i q
  exact Eq.mp (congrArg₂ (Reachable (atlas v hP hT).board (some 1)) hp hq) hh

/-- In every actual mixed atlas inventory, the full-gate core player communicates with all four literal macrocell corners, retaining every box on the board. -/
theorem gate_profile_corners (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1) (c : Fin 4) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells (fullAtlas (gateTileState (g,v.2))).player))
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells (outerCorner c))) ∧
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells (outerCorner c)))
      ((atlas v hP hT).profileAt f ((gateEmbedding v g hg).cells (fullAtlas (gateTileState (g,v.2))).player)) := by
  have hh:=masked_exterior_corners (gateTileState (g,v.2)) (fun _=>f (numbering v (gateIndex v g hg)))
    (gateProfileFixed v hP hT f g hg) (gate_profile_fixed_mask v hP hT f g hg) c
  exact ⟨gate_profile_walk v hP hT f g hg _ _ hh.1,gate_profile_walk v hP hT f g hg _ _ hh.2⟩

end PushPuzzle.PushFS.Reduction.PhysicalInventory

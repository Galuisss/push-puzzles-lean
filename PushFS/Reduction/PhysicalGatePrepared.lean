/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateForeign
public import PushFS.Reduction.PhysicalGatePreparedGeometry

/-! Actual neighboring selected wire phases prepare the strict external collar of a changing full-gate arm. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 1000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board
  StorageAtlas.profileOutside StorageAtlas.profileBoxes gateProfileFixed

/-- The one ordinary source neighbor at this actual port has its released source/target phase. -/
def GatePortReleased (v : CellPlan.Source) (f : Fin (Fintype.card (Index v))→Bool)
    (g : VertexData) (role : Fin 3) : Prop :=
  ∀j : Index v,∀a : Catalog.Bitmap.Args,tile j=.inr a→
    neighbor (g.portDirection role) (refinePoint g.point)=some (position j)→
      PhysicalTiles.wirePhase a (f (numbering v j))= !((gateTileState (g,v.2)).incoming.get role)

/-- The entire real foreign atlas inventory meets every line of a released gate arm only in its strict macro collar. -/
theorem gate_profile_released_collar (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (g : VertexData) (hg : g∈vertexRecords v.1)
    (role : Fin 3) (released : GatePortReleased v f g role)
    (j : Fin (curve (GateTileRouting.key (gateTileState (g,v.2)) role)).length)
    (p : Cell (lineInput (gateTileState (g,v.2)) role j).width (lineInput (gateTileState (g,v.2)) role j).height)
    (hp : (lineEmbedding (gateTileState (g,v.2)) role j).cells p∈gateProfileFixed v hP hT f g hg) :
    p∈lineNeighbors (fillerFlip (GateTileRouting.key (gateTileState (g,v.2)) role) j.val)
      (fillerSpan (GateTileRouting.key (gateTileState (g,v.2)) role) j.val)
      (filler_shape _ _ j.isLt).2.1 (Inventory.initialPhase (gateTileState (g,v.2)) role)
      (Inventory.targetPhase (gateTileState (g,v.2)) role) := by
  let q:=(lineEmbedding (gateTileState (g,v.2)) role j).cells p
  have hp':=(mem_gateProfileFixed v hP hT f g hg q).mp hp
  obtain ⟨i,hi,s,hs,he⟩:=profile_foreign v hP hT f (gateIndex v g hg) q hp'
  rcases i with ⟨⟨pos,h|a⟩,hkey⟩
  · have hpos:=PhysicalTiles.gate_gate_overlap (key_eq (gateIndex v g hg)) hkey q s he
    exact (hi (position_injective hpos.symm)).elim
  · obtain ⟨l,hl⟩:=PhysicalTiles.mark_slot _ _ s hs
    rw [←hl] at he
    have hn:=PhysicalTiles.gate_line_foreign_neighbor v (key_eq (gateIndex v g hg)) hkey role j p _ he
    have hphase:=released ⟨(pos,.inr a),hkey⟩ a rfl hn
    exact PhysicalTiles.gate_released_line_collar v hP hT (key_eq (gateIndex v g hg)) hkey role hn _ l j p hphase he

end PushPuzzle.PushFS.Reduction.PhysicalInventory

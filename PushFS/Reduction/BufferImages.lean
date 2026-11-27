/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.BufferSourceComponents
public import PushFS.Reduction.PhysicalImages
public import PushFS.Gadgets.Wires.Catalog.RotatedChainSignal

/-! Every actual buffered lead retains its native complete chain storage image and orientation. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets Gadgets.Wires Catalog
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] StorageAtlas.initial StorageAtlas.board

def bufferImage (g : GateTileState) (r : Fin 3) :
    StorageImage (rawSlotMatching g)
      ((Chain.slotMatching 2301 (by omega) (Inventory.initialPhase g r) (Inventory.targetPhase g r)).reorient
        ((frontierOrientation g.core.isAND r).axis 2306 21).geometry) := by
  rcases g with ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  refine Fin.cases ?_ (Fin.cases ?_ (fun z=>?_)) r
  · cases kind <;> exact primitiveRawImage _ (.inl 1)
  · cases kind <;> exact primitiveRawImage _ (.inl 2)
  · have hz : z=0 := by apply Fin.ext; have h:=z.isLt; omega
    subst z
    cases kind <;> exact primitiveRawImage _ (.inl 3)

theorem bufferImage_labels (g : GateTileState) (r : Fin 3) (l : Chain.Label 2301) :
    (bufferImage g r).labels l=bufferLabel g r l := by
  rcases g with ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  fin_cases r <;> cases kind <;> rfl

theorem bufferImage_point (g : GateTileState) (r : Fin 3) (p : Chain.C 2301) :
    (bufferImage g r).orientedPoint (frontierOrientation g.core.isAND r) p=
      (bufferLeadEmbedding g r).cells p := by
  rcases g with ⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  let G : GateTileState:=⟨⟨kind,a,b⟩,incoming,pattern,rotation⟩
  fin_cases r
  · cases kind <;> exact buffer_lead_placement G 0 p
  · cases kind <;> exact buffer_lead_placement G 1 p
  · cases kind <;> exact buffer_lead_placement G 2 p

theorem frontier_outward (kind : Bool) (r : Fin 3) :
    (frontierOrientation kind r).direction .east=Gates.portDirection r := by
  fin_cases r <;> cases kind <;> rfl

end PushPuzzle.PushFS.Reduction.GateTileRouting

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires Catalog
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

end PushPuzzle.PushFS.Reduction.PhysicalInventory

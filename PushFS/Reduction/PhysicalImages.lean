/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalRawLabels
public import PushFS.Reduction.AnnulusRawFrames
public import PushFS.Gadgets.Wires.Catalog.RectImages

/-! Exact complete physical source-cell and gate-primitive storage images for ambient signal proofs. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.GateTileRouting

open Gadgets.Wires.Catalog
set_option maxRecDepth 65536

def primitiveRawImage (g : GateTileState) (i : Inventory.Index g) :
    StorageImage (rawSlotMatching g) (Inventory.matching g i) where
  dx:=(Inventory.offset g i).1
  dy:=(Inventory.offset g i).2
  fit_x:=(Inventory.fits g i).1
  fit_y:=(Inventory.fits g i).2
  labels:=⟨fun l=>⟨i,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
  walls:=primitive_walls_agree g i
  sources:=raw_source g i
  targets:=raw_target g i

end PushPuzzle.PushFS.Reduction.GateTileRouting

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory
open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

noncomputable def tileImage (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) : Catalog.StorageImage (rawSlotMatching v hP hT) (PhysicalTiles.matching (tile (v:=v) i)) where
  dx:=(PhysicalTiles.offset (position i) (tile (v:=v) i)).1
  dy:=(PhysicalTiles.offset (position i) (tile (v:=v) i)).2
  fit_x:=(PhysicalTiles.fits v.1 i.val.1 (tile i)).1
  fit_y:=(PhysicalTiles.fits v.1 i.val.1 (tile i)).2
  labels:=⟨fun l=>⟨i,l⟩,fun _ _ he=>eq_of_heq (Sigma.mk.inj he).2⟩
  walls:=walls_agree v hP hT i
  sources:=raw_source v hP hT i
  targets:=raw_target v hP hT i

noncomputable def gateImage (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) :
    Catalog.StorageImage (rawSlotMatching v hP hT) (GateTileRouting.rawSlotMatching (gateTileState (g,v.2))) :=
  (tileImage v hP hT (gateIndex v g hg)).relabel (GateTileRouting.rawLabelEquiv (gateTileState (g,v.2)))

end PushPuzzle.PushFS.Reduction.PhysicalInventory

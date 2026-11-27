/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalWireMacros

/-! Actual predecessor, successor and released gate phases prepare the complete ordinary-macrocell foreign inventory. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

structure WirePrepared (v : CellPlan.Source) (f : Fin (Fintype.card (Index v))→Bool)
    (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args) : Prop where
  predecessor : ∀(j : Index v) (b : Catalog.Bitmap.Args),tile j=.inr b→
    neighbor (Catalog.sourceDirection a.1).opposite (p.1.val,p.2.val)=some (position j)→
      PhysicalTiles.wirePhase b (f (numbering v j))=false
  successor : ∀(j : Index v) (b : Catalog.Bitmap.Args),tile j=.inr b→
    neighbor (Catalog.targetDirection a.1) (p.1.val,p.2.val)=some (position j)→
      PhysicalTiles.wirePhase b (f (numbering v j))=true
  gate : ∀(j : Index v) (g : GateTileState),tile j=.inl g→∀r : Fin 3,
    neighbor (PortAnnulus.outerDirection (g.key r).2) (position j)=some (p.1.val,p.2.val)→
      PhysicalTiles.gatePhase g (f (numbering v j)) r=false
end PushPuzzle.PushFS.Reduction.PhysicalInventory

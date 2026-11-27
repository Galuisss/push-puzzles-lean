/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalProfileForeign
public import PushFS.Reduction.PhysicalWireForeignGeometry
public import PushFS.Reduction.PhysicalWireSignals

/-! Every actual foreign mixed-profile slot in an ordinary tile lies on its real native walking collar. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

theorem wire_foreign_walkingMask (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (q : Catalog.Cell) (hq : (embedding v (wireIndex v p a ha)).cells q∈
      (atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))) : Catalog.WalkingMask a.1 q := by
  let i:=wireIndex v p a ha
  obtain ⟨j,hji,s,hs,he⟩:=profile_foreign v hP hT f i q hq
  have hpos : position i≠position j:=fun hp=>hji (position_injective hp).symm
  have hk:=key_eq j
  generalize htile : tile j=k at s hs he hk
  rcases k with g|b
  · obtain ⟨l,rfl⟩:=PhysicalTiles.mark_slot (f (numbering v j)) (.inl g) s hs
    obtain ⟨_,_,hm,_⟩:=PhysicalTiles.wire_foreign_gate_data v hP hT hk ha (f (numbering v j)) l q he.symm
    exact hm
  · obtain ⟨l,rfl⟩:=PhysicalTiles.mark_slot (f (numbering v j)) (.inr b) s hs
    exact PhysicalTiles.wire_foreign_wire_mask v hP hT ha hk hpos (f (numbering v j)) l q he
end PushPuzzle.PushFS.Reduction.PhysicalInventory

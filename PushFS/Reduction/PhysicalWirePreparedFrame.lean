/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalWirePrepared
public import PushFS.Reduction.PhysicalWireForeign

/-! Actual prepared selected neighbor phases instantiate every native ordinary-cell collar and complete tile replay. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires
set_option maxRecDepth 65536
set_option maxHeartbeats 2000000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

/-- Actual selected neighbor phases imply the strict foreign-mask preparation of every native primitive. -/
private theorem wire_prepared_mask (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) (prepared : WirePrepared v f p a)
    (q : Catalog.Cell) (hq : (embedding v (wireIndex v p a ha)).cells q∈
      (atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))) : Catalog.PreparedMask a.1 q := by
  let i:=wireIndex v p a ha
  obtain ⟨j,hji,s,hs,he⟩:=profile_foreign v hP hT f i q hq
  have hpos : position i≠position j:=fun hp=>hji (position_injective hp).symm
  have hk:=key_eq j
  generalize htile : tile j=k at s hs he hk
  rcases k with g|b
  · obtain ⟨l,rfl⟩:=PhysicalTiles.mark_slot (f (numbering v j)) (.inl g) s hs
    obtain ⟨r,hn,_,hm⟩:=PhysicalTiles.wire_foreign_gate_data v hP hT hk ha (f (numbering v j)) l q he.symm
    exact hm (prepared.gate j g htile r hn)
  · obtain ⟨l,rfl⟩:=PhysicalTiles.mark_slot (f (numbering v j)) (.inr b) s hs
    exact PhysicalTiles.wire_foreign_wire_prepared v hP hT ha hk hpos (f (numbering v j)) l q
      (prepared.predecessor j b htile) (prepared.successor j b htile) he

/-- A true ordinary tile update needs only its actual predecessor, successor and gate phase contracts. -/
theorem wire_update (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hi : f (numbering v (wireIndex v p a ha))=false) (prepared : WirePrepared v f p a) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player))
      ((atlas v hP hT).profileAt (Function.update f (numbering v (wireIndex v p a ha)) true)
        ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player)) :=
  wire_update_at v hP hT f p a ha hi (wire_prepared_mask v hP hT f p a ha prepared)
end PushPuzzle.PushFS.Reduction.PhysicalInventory

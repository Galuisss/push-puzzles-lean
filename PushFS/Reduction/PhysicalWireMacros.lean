/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalProfileForeign
public import PushFS.Reduction.PhysicalWireSignals
public import PushFS.Gadgets.Wires.Catalog.PreparedMasks

/-! Every actual ordinary macrocell updates its complete owned inventory with every foreign physical box retained. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires Catalog
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

theorem profile_place_source_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v) (hi : f (numbering v i)=false) :
    (embedding v i).extend ((atlas v hP hT).profileOutside f (numbering v i)) (PhysicalTiles.piece (tile i)).initial=
      (atlas v hP hT).profileAt f ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player) := by
  obtain ⟨j,rfl⟩:=(numbering v).symm.surjective i
  have hj : f j=false:=by simpa only [Equiv.apply_symm_apply] using hi
  have he:=(atlas v hP hT).profile_place_source f j hj
  change (embedding v ((numbering v).symm j)).extend ((atlas v hP hT).profileOutside f j)
    (PhysicalTiles.piece (tile ((numbering v).symm j))).initial=
      (atlas v hP hT).profileAt f ((embedding v ((numbering v).symm j)).cells
        (PhysicalTiles.piece (tile ((numbering v).symm j))).initial.player) at he
  simpa only [Equiv.apply_symm_apply] using he

theorem profile_place_target_index (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (i : Index v) :
    (embedding v i).extend ((atlas v hP hT).profileOutside f (numbering v i))
      ⟨(PhysicalTiles.piece (tile i)).initial.player,(PhysicalTiles.piece (tile i)).board.goals⟩=
      (atlas v hP hT).profileAt (Function.update f (numbering v i) true)
        ((embedding v i).cells (PhysicalTiles.piece (tile i)).initial.player) := by
  obtain ⟨j,rfl⟩:=(numbering v).symm.surjective i
  have he:=(atlas v hP hT).profile_place_target f j
  change (embedding v ((numbering v).symm j)).extend ((atlas v hP hT).profileOutside f j)
    ⟨(PhysicalTiles.piece (tile ((numbering v).symm j))).initial.player,
      (PhysicalTiles.piece (tile ((numbering v).symm j))).board.goals⟩=
      (atlas v hP hT).profileAt (Function.update f j true)
        ((embedding v ((numbering v).symm j)).cells (PhysicalTiles.piece (tile ((numbering v).symm j))).initial.player) at he
  simpa only [Equiv.apply_symm_apply] using he

/-- Literal prepared endpoint slots instantiate all seven native thin frames on the actual complete board. -/
private theorem wire_frame (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped []
    [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (prepared : ∀q : Catalog.Cell,(embedding v (wireIndex v p a ha)).cells q∈
      (atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))→Catalog.PreparedMask a.1 q) :
    Catalog.AmbientFrame a.1 a.2.1 a.2.2 (embedding v (wireIndex v p a ha)) (atlas v hP hT).board
      ((atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))) := by
  exact Catalog.ambientFrame_of_prepared _ _ _ _ (walls_agree v hP hT (wireIndex v p a ha))
    ((atlas v hP hT).profileOutside_floor f _) (Catalog.prepared_of_mask _ _ _ _ _ prepared)

/-- A prepared actual ordinary tile changes its entire inventory and leaves the exact complete foreign profile fixed. -/
theorem wire_update_at (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (f : Fin (Fintype.card (Index v))→Bool) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hi : f (numbering v (wireIndex v p a ha))=false)
    (prepared : ∀q : Catalog.Cell,(embedding v (wireIndex v p a ha)).cells q∈
      (atlas v hP hT).profileOutside f (numbering v (wireIndex v p a ha))→Catalog.PreparedMask a.1 q) :
    Reachable (atlas v hP hT).board (some 1)
      ((atlas v hP hT).profileAt f ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player))
      ((atlas v hP hT).profileAt (Function.update f (numbering v (wireIndex v p a ha)) true)
        ((embedding v (wireIndex v p a ha)).cells (Catalog.puzzle a.1 a.2.1 a.2.2).initial.player)) := by
  have hr:=Catalog.ambient_transition a.1 a.2.1 a.2.2 (embedding v (wireIndex v p a ha))
    (wire_frame v hP hT f p a ha prepared)
  have hs:=profile_place_source_index v hP hT f (wireIndex v p a ha) hi
  have ht:=profile_place_target_index v hP hT f (wireIndex v p a ha)
  exact hs ▸ht ▸hr
end PushPuzzle.PushFS.Reduction.PhysicalInventory

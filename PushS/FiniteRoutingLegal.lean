/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingWireGeometry
public import PushS.FiniteRoutingGateGeometry
public import PushS.FiniteSourcePlayer

/-! Actual complete wire inventories satisfy all finite storage-instance validity conditions. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

/-- Every emitted complete three-arm gate is an admissible physical storage inventory. -/
theorem gateInventory_admissible (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    (gateInventory w hw g).Admissible := by
  have hc := gateInventory_actorsClear w hw g
  have hx (i : Fin (gateCodes w g).length) : 0 < (gateInventory w hw g).dx i :=
    (gateCode_offset_pos w g (List.get_mem (gateCodes w g) i)).1
  exact ⟨hc.source_injective,hc.target_injective,hc.source_floor,hc.target_floor,
    (gateInventory w hw g).player_floor_of_dx_pos rfl hx,
    (gateInventory w hw g).player_empty_of_dx_pos rfl hx⟩

/-- Every one of the seven emitted wire tables is an admissible complete physical storage inventory. -/
theorem wireInventory_admissible (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    (wireInventory w hw q).Admissible := by
  have hc := wireInventory_actorsClear w hw q
  have hx (i : Fin (wireCodes w q).length) : 0 < (wireInventory w hw q).dx i :=
    (wireCode_offset_pos w q (List.get_mem (wireCodes w q) i)).1
  exact ⟨hc.source_injective,hc.target_injective,hc.source_floor,hc.target_floor,
    (wireInventory w hw q).player_floor_of_dx_pos rfl hx,
    (wireInventory w hw q).player_empty_of_dx_pos rfl hx⟩

end PushPuzzle.PushS.FiniteRouting

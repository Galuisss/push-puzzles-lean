/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPieces
public import PushFS.Reduction.InventoryAssembly

/-! The actual emitted primitive lists as complete semantic tile inventories. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

/-- Physical identities retain their literal emitted primitive index. -/
def PieceLabel (w : ℕ) (codes : List PrimitiveCode) (i : Fin codes.length) : Type :=
  (codes.get i).Labels w

instance (w : ℕ) (codes : List PrimitiveCode) (i : Fin codes.length) : Fintype (PieceLabel w codes i) :=
  inferInstanceAs (Fintype ((codes.get i).Labels w))

/-- All actual primitive walls and owned boxes before geometric clearance is certified. -/
def inventory (w : ℕ) (hw : 2 ≤ w) (codes : List PrimitiveCode)
    (hf : ∀ c ∈ codes, PatchFits w (c.patch w hw)) :
    InventoryAssembly codes.length (tileSide w) (tileSide w) (PieceLabel w codes) where
  piece i := (codes.get i).instanceOf w hw
  matching i := (codes.get i).matching w hw
  dx i := (codes.get i).offsetX w
  dy i := (codes.get i).offsetY w
  fitsX i := (hf (codes.get i) (List.get_mem _ _)).1
  fitsY i := (hf (codes.get i) (List.get_mem _ _)).2
  player := (⟨0, by unfold tileSide; omega⟩, ⟨0, by unfold tileSide; omega⟩)

/-- The full three-arm gate inventory is indexed by exactly the emitted primitive code list. -/
def gateInventory (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) :
    InventoryAssembly (gateCodes w g).length (tileSide w) (tileSide w) (PieceLabel w (gateCodes w g)) :=
  inventory w hw (gateCodes w g) (fun _ hc => gateCode_fits w hw g hc)

def wireInventory (w : ℕ) (hw : 2 ≤ w) (q : Catalog.Bitmap.Args) :
    InventoryAssembly (wireCodes w q).length (tileSide w) (tileSide w) (PieceLabel w (wireCodes w q)) :=
  inventory w hw (wireCodes w q) (fun _ hc => wireCode_fits w hw q hc)

end PushPuzzle.PushS.FiniteRouting

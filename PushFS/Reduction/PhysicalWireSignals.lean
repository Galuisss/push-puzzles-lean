/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalImages
public import PushFS.Gadgets.Wires.Catalog.Signal

/-! Every actual ordinary source-cell instruction supplies its full physical near-to-far successful-path signal. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open PhysicalBitmap Gadgets.Wires Catalog Soundness
attribute [local irreducible] Raster.width Raster.height

def wireIndex (v : CellPlan.Source) (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) : Index v :=
  ⟨(p,.inr a),ha⟩

theorem wire_signal (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) (cert : Certificate (puzzle v hP hT))
    (ordered : (rawSlotMatching v hP hT).Ordered) :
    let image:=tileImage v hP hT (wireIndex v p a ha)
    Catalog.sourceHigh a.1 image.dx image.dy (S.position (image.labels (Catalog.firstLabel a.1)))→
      Catalog.targetHigh a.1 image.dx image.dy (S.position (image.labels (Catalog.lastLabel a.1))) := by
  exact Catalog.signal (tileImage v hP hT (wireIndex v p a ha)) hs cert ordered

end PushPuzzle.PushFS.Reduction.PhysicalInventory

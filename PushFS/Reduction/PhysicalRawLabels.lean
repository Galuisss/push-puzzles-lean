/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalGatePlacement
public import PushFS.Reduction.FullGateRawLabels

/-! Real source-cell and primitive identities in the complete physical source board. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL Plan PhysicalBitmap
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

abbrev RawLabel (v : CellPlan.Source) := (i : Index v)×PhysicalTiles.Labels (tile (v := v) i)

noncomputable instance (v : CellPlan.Source) : Fintype (RawLabel v) := by
  unfold RawLabel
  infer_instance

noncomputable def rawLabelEquiv (v : CellPlan.Source) :
    RawLabel v≃((j : Fin (Fintype.card (Index v)))×Labels v j) :=
  Equiv.sigmaCongrLeft' (numbering v)

noncomputable def rawSlotMatching (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) :
    SlotMatching (puzzle v hP hT) (RawLabel v) :=
  (slotMatching v hP hT).relabel (rawLabelEquiv v)

noncomputable def rawSource (v : CellPlan.Source) (l : RawLabel v) :
    Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  (embedding v l.1).cells ((PhysicalTiles.matching (tile (v := v) l.1)).source l.2)

noncomputable def rawTarget (v : CellPlan.Source) (l : RawLabel v) :
    Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7) :=
  (embedding v l.1).cells ((PhysicalTiles.matching (tile (v := v) l.1)).target l.2)

theorem raw_source (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (l : PhysicalTiles.Labels (tile (v := v) i)) :
    (rawSlotMatching v hP hT).source ⟨i,l⟩=rawSource v ⟨i,l⟩ := by
  change rawSource v ((rawLabelEquiv v).symm ((rawLabelEquiv v) ⟨i,l⟩))=rawSource v ⟨i,l⟩
  rw [Equiv.symm_apply_apply]

theorem raw_target (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (i : Index v) (l : PhysicalTiles.Labels (tile (v := v) i)) :
    (rawSlotMatching v hP hT).target ⟨i,l⟩=rawTarget v ⟨i,l⟩ := by
  change rawTarget v ((rawLabelEquiv v).symm ((rawLabelEquiv v) ⟨i,l⟩))=rawTarget v ⟨i,l⟩
  rw [Equiv.symm_apply_apply]

noncomputable def gateLabel (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1)
    (l : GateTileRouting.RawLabel (gateTileState (g,v.2))) : RawLabel v :=
  ⟨gateIndex v g hg,GateTileRouting.rawLabelEquiv (gateTileState (g,v.2)) l⟩

theorem gateLabel_source (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    (i : GateTileRouting.Inventory.Index (gateTileState (g,v.2)))
    (l : GateTileRouting.Inventory.Labels (gateTileState (g,v.2)) i) :
    (rawSlotMatching v hP hT).source (gateLabel v g hg ⟨i,l⟩)=
      (gatePrimitiveEmbedding v g hg i).cells ((GateTileRouting.Inventory.matching (gateTileState (g,v.2)) i).source l) := by
  rw [raw_source]
  have hh := GateTileRouting.raw_source (gateTileState (g,v.2)) i l
  exact congrArg (gateEmbedding v g hg).cells hh

theorem gateLabel_target (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    (i : GateTileRouting.Inventory.Index (gateTileState (g,v.2)))
    (l : GateTileRouting.Inventory.Labels (gateTileState (g,v.2)) i) :
    (rawSlotMatching v hP hT).target (gateLabel v g hg ⟨i,l⟩)=
      (gatePrimitiveEmbedding v g hg i).cells ((GateTileRouting.Inventory.matching (gateTileState (g,v.2)) i).target l) := by
  rw [raw_target]
  have hh := GateTileRouting.raw_target (gateTileState (g,v.2)) i l
  exact congrArg (gateEmbedding v g hg).cells hh

end PushPuzzle.PushFS.Reduction.PhysicalInventory

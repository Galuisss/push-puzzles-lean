/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTriggerReadout
public import PushFS.Reduction.PhysicalGateReadout

/-! Actual successful thick-gate observations satisfy every original finite NCL vertex constraint. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGateReadout
open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalInventory
open PushFS.Gadgets PushFS.Gadgets.Wires.Soundness

attribute [local irreducible] codes width height Raster.width Raster.height InventoryAssembly.board InventoryAssembly.walls

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

/-- The three actual core thresholds observed at an original vertex record. -/
@[expose]
noncomputable def observedSignals (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g ∈ vertexRecords v.1)
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)) : Gates.Signals :=
  (recordSite w hw v g hg).boundarySignals hP hT S

private theorem observedSignals_legal (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (ha : (Word.compile v.1).checkLegal v.initialBits = true) (hb : (Word.compile v.1).checkLegal v.targetBits = true)
    (g : VertexData) (hg : g ∈ vertexRecords v.1)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final) :
    Gates.legal g.ports.isAND (observedSignals w hw v hP hT g hg S) :=
  (recordSite w hw v g hg).boundary_legal hP hT h
    (record_legal v.1 hvalid hP hT v.initialBits ha g hg) (record_legal v.1 hvalid hP hT v.targetBits hb g hg)

/-- The original finite source reads legal weighted claims throughout every actual successful path. -/
theorem sourceReadout_legal (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed)
    (ha : (Word.compile v.1).checkLegal v.initialBits = true) (hb : (Word.compile v.1).checkLegal v.targetBits = true)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final) :
    PortClaims.Legal (Word.compile v.1).graph ((sourceReadout w hw v hvalid hP hT hG).read S) :=
  PhysicalInventory.record_claims_legal v.1 hvalid hP hT ((sourceReadout w hw v hvalid hP hT hG).read S)
    (fun g hg => observedSignals w hw v hP hT g hg S) (sourceReadout_incidence w hw v hvalid hP hT hG S)
    (fun g hg => observedSignals_legal w hw v hvalid hP hT ha hb g hg h)

end PushPuzzle.PushS.FiniteSourceInventory

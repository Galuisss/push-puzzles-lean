/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalBufferSignals
public import PushFS.Reduction.FrontierSignalSeam
public import PushFS.Reduction.AnnulusOuterSignals

/-! Actual core source observations reach the literal outer endpoint identities and thresholds of the full physical gate. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

noncomputable def outerLabel (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) : RawLabel v :=
  gateLabel v g hg (GateTileRouting.outerEndpointLabel (gateTileState (g,v.2)) r)

theorem outerLabel_source_coordinates (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) :
    let s:=gateTileState (g,v.2)
    let p:=GateTileRouting.FullGateBoundary.endpointPoint (PortAnnulus.outerDirection (s.key r).2)
      (s.incoming.get r) (GateTileRouting.Inventory.initialPhase s r) false
    let q:=(rawSlotMatching v hP hT).source (outerLabel v g hg r)
    (q.1.val,q.2.val)=(strideX*(refinePoint g.point).1+p.1,strideY*(refinePoint g.point).2+p.2) := by
  let s:=gateTileState (g,v.2)
  have hs:=(gateImage v hP hT g hg).sources (GateTileRouting.outerEndpointLabel s r)
  have hl:=GateTileRouting.outer_source_coordinates s r
  have hxy:=congrArg (fun p : Cell (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)=>(p.1.val,p.2.val)) hs
  exact hxy.trans (congrArg (fun p : ℕ×ℕ=>(strideX*(refinePoint g.point).1+p.1,strideY*(refinePoint g.point).2+p.2)) hl)

theorem outerHigh_iff (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) (r : Fin 3) :
    let s:=gateTileState (g,v.2)
    let p:=GateTileRouting.FullGateBoundary.endpointPoint (PortAnnulus.outerDirection (s.key r).2) (s.incoming.get r) true false
    GateTileRouting.OuterHigh (gateImage v hP hT g hg) S r ↔
      TravelHigh (PortAnnulus.outerDirection (s.key r).2)
        (strideX*(refinePoint g.point).1+p.1,strideY*(refinePoint g.point).2+p.2)
        ((S.position (outerLabel v g hg r)).1.val,(S.position (outerLabel v g hg r)).2.val) := by
  rfl

/-- The exact original source incidence forces its genuine outer endpoint, through every complete auxiliary inventory. -/
theorem observed_to_outer (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) (r : Fin 3)
    (hin : gateClaim (observedSignals v g hg S) r=true) :
    GateTileRouting.OuterHigh (gateImage v hP hT g hg) S r := by
  have hb:=observed_to_buffer v hP hT g hg hs r hin
  have ha:=GateTileRouting.buffer_to_arm (gateImage v hP hT g hg) r hs (certificate v hP hT)
    (matching_ordered v hP hT) hb
  exact GateTileRouting.arm_to_outer (gateImage v hP hT g hg) S r ha

end PushPuzzle.PushFS.Reduction.PhysicalInventory

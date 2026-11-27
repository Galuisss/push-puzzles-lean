/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.BufferTravelSignals
public import PushFS.Reduction.PhysicalSoundness
public import PushFS.Reduction.PhysicalCoreTags
public import PushFS.Reduction.PhysicalOrder

/-! Actual source incidence thresholds reach the far endpoints of all three complete physical buffered leads. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets Gadgets.Wires Catalog Gates.Soundness Wires.Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem coreAnchor_coordinates (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) :
    let p:=GateTileRouting.coreAnchor (gateImage v hP hT g hg) r
    (p.1.val,p.2.val)=
      ((coreOffset g).1+(GateTileRouting.coreGhost g.ports.isAND r).1.val,
        (coreOffset g).2+(GateTileRouting.coreGhost g.ports.isAND r).2.val) :=
  core_coordinates v g hg (GateTileRouting.coreGhost g.ports.isAND r)

private theorem boundary_high {I : Instance} {L : Type} [Fintype L] {M : SlotMatching I L}
    {A : AxisTracks I} {kind : Bool} (c : GateGlyph M A kind)
    (S : LabelledState L I.width I.height) (r : Fin 3) :
    TravelHigh (Gates.portDirection r)
      (c.dx+(GateTileRouting.coreGhost kind r).1.val,c.dy+(GateTileRouting.coreGhost kind r).2.val)
      ((S.position (c.labels (Relay.outerLabel kind r))).1.val,(S.position (c.labels (Relay.outerLabel kind r))).2.val) ↔
      c.boundarySignal S r=true := by
  fin_cases r <;> cases kind <;>
    simp [TravelHigh,Gates.portDirection,GateTileRouting.coreGhost,GateGlyph.boundarySignal]

private theorem coreHigh_iff_boundary (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) (r : Fin 3) :
    GateTileRouting.CoreHigh (gateImage v hP hT g hg) S r ↔
      (coreGlyph v hP hT (axisTracks v hP hT) g hg (coreTags v hP hT g hg)).boundarySignal S r=true := by
  have hh:=boundary_high (coreGlyph v hP hT (axisTracks v hP hT) g hg (coreTags v hP hT g hg)) S r
  change TravelHigh (Gates.portDirection r)
    ((coreOffset g).1+(GateTileRouting.coreGhost g.ports.isAND r).1.val,
      (coreOffset g).2+(GateTileRouting.coreGhost g.ports.isAND r).2.val)
    ((S.position ((gateImage v hP hT g hg).labels (GateTileRouting.coreEndpointLabel (gateTileState (g,v.2)) r))).1.val,
      (S.position ((gateImage v hP hT g hg).labels (GateTileRouting.coreEndpointLabel (gateTileState (g,v.2)) r))).2.val) ↔_
    at hh
  unfold GateTileRouting.CoreHigh
  exact (coreAnchor_coordinates v hP hT g hg r).symm ▸hh

theorem observed_to_buffer (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) (r : Fin 3)
    (hin : gateClaim (observedSignals v g hg S) r=true) :
    GateTileRouting.BufferHigh (gateImage v hP hT g hg) S r true := by
  have hc:=observed_to_core_boundary v hP hT (axisTracks v hP hT) g hg (coreTags v hP hT g hg)
    (certificate v hP hT) (matching_ordered v hP hT) hs r hin
  exact GateTileRouting.core_to_buffer_signal (gateImage v hP hT g hg) r hs (certificate v hP hT)
    (matching_ordered v hP hT) ((coreHigh_iff_boundary v hP hT g hg S r).mpr hc)

end PushPuzzle.PushFS.Reduction.PhysicalInventory

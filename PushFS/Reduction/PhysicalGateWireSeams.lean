/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.GateWireSeamGeometry
public import PushFS.Reduction.PhysicalOuterSignals
public import PushFS.Reduction.PhysicalWireSeams

/-! Actual original-source gate/wire incidences preserve physical source components and their asymmetric endpoint signals. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires Catalog Soundness GateTileRouting
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

/-- The physical adjacent wire has the exact original port edge, flow and endpoint phase. -/
private theorem gate_wire_contract (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (p : Raster.Cell v.1)
    (e : ℕ) (a : Catalog.Bitmap.Args)
    (hc : CellPlan.cell (v,(p.1.val,p.2.val))=some (.inr (e,a)))
    (hn : neighbor (g.portDirection r) (refinePoint g.point)=some (p.1.val,p.2.val)) :
    (g.ports.port r).edge=e ∧
    GateWireGeometry.Flow (g.portDirection r) ((gateTileState (g,v.2)).incoming.get r) a.1 ∧
    Inventory.initialPhase (gateTileState (g,v.2)) r=
      (if (gateTileState (g,v.2)).incoming.get r then !a.2.1 else a.2.1) ∧Catalog.Straight a.1 := by
  obtain ⟨he,hf⟩:=CellPlan.gate_adjacent v hP hT hg r hn hc
  have ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a):=by rw [hc]; rfl
  have hp : PhysicalTiles.gatePhase (gateTileState (g,v.2)) false r=
      if (gateTileState (g,v.2)).incoming.get r then !(PhysicalTiles.wirePhase a false)
        else PhysicalTiles.wirePhase a false := by
    rw [gateTileState_incoming,PhysicalTiles.wire_phase hc false,←he]
    exact PhysicalTiles.gate_phase v g false r
  refine ⟨he,?_,hp,?_⟩
  · unfold GateWireGeometry.Flow
    rw [gateTileState_incoming]
    exact hf
  · exact PhysicalTiles.gate_neighbor_straight v hP hT hn (gateIndex v g hg).property ha

private theorem gate_wire_source_component (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (p : Raster.Cell v.1)
    (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hn : neighbor (g.portDirection r) (refinePoint g.point)=some (p.1.val,p.2.val)) :
    let s:=gateTileState (g,v.2)
    let image:=tileImage v hP hT (wireIndex v p a ha)
    let l:=if s.incoming.get r then lastLabel a.1 else firstLabel a.1
    component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source (outerLabel v g hg r))=
      component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source (image.labels l)) := by
  obtain ⟨e,hc⟩:=PhysicalTiles.wire_code ha
  obtain ⟨_,hflow,hphase,hstraight⟩:=gate_wire_contract v hP hT g hg r p e a hc hn
  let s:=gateTileState (g,v.2)
  let d:=g.portDirection r
  let inc:=s.incoming.get r
  let b:=Inventory.initialPhase s r
  let f:=gateImage v hP hT g hg
  let image:=tileImage v hP hT (wireIndex v p a ha)
  let chart:=FullGateStatics.ribbonChart d
  have hlocal:=GateWireGeometry.ribbon_component d inc b
  have hwall:=FullGateStatics.ribbon_walls s d ⟨r,rfl⟩
  have hgcomp : SameComponent (fullPuzzle s).board
      (chart.embedding.cells (GateWireGeometry.ribbonGate d inc b))
      (chart.embedding.cells (GateWireGeometry.ribbonWire d inc b)) :=
    ⟨GridEmbedding.staticReach hwall hlocal.1,GridEmbedding.staticReach hwall hlocal.2⟩
  have hcomp : SameComponent (puzzle v hP hT).board
      (f.point (chart.embedding.cells (GateWireGeometry.ribbonGate d inc b)))
      (f.point (chart.embedding.cells (GateWireGeometry.ribbonWire d inc b))) :=
    ⟨GridEmbedding.staticReach f.walls hgcomp.1,GridEmbedding.staticReach f.walls hgcomp.2⟩
  have hgate : (rawSlotMatching v hP hT).source (outerLabel v g hg r)=
      f.point (chart.embedding.cells (GateWireGeometry.ribbonGate d inc b)) := by
    have hx:=outerLabel_source_coordinates v hP hT g hg r
    have hy:=GateWireGeometry.ribbon_gate_coordinates d inc b
    apply Prod.ext <;> apply Fin.ext
    · exact (congrArg Prod.fst hx).trans (congrArg (fun q : ℕ×ℕ=>strideX*(refinePoint g.point).1+q.1) hy.symm)
    · exact (congrArg Prod.snd hx).trans (congrArg (fun q : ℕ×ℕ=>strideY*(refinePoint g.point).2+q.2) hy.symm)
  have hwire : f.point (chart.embedding.cells (GateWireGeometry.ribbonWire d inc b))=
      (rawSlotMatching v hP hT).source (image.labels (if inc then lastLabel a.1 else firstLabel a.1)) := by
    have hw:=wire_source_coordinates v hP hT p a ha inc
    have hx:=GateWireGeometry.ghost_coordinates (refinePoint g.point) (p.1.val,p.2.val) d inc a.2.1 a.1 hstraight hn hflow
    have hp : b=(if inc then !a.2.1 else a.2.1):=hphase
    rw [←hp] at hx
    have he:=hx.trans hw.symm
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst he
    · exact congrArg Prod.snd he
  apply component_eq_iff.mpr
  exact hgate.symm ▸hwire ▸hcomp

private theorem gate_wire_source_order (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (p : Raster.Cell v.1)
    (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hn : neighbor (g.portDirection r) (refinePoint g.point)=some (p.1.val,p.2.val)) :
    let s:=gateTileState (g,v.2)
    let image:=tileImage v hP hT (wireIndex v p a ha)
    let l:=if s.incoming.get r then lastLabel a.1 else firstLabel a.1
    DirectionalOrder (g.portDirection r)
      (((rawSlotMatching v hP hT).source (outerLabel v g hg r)).1.val,((rawSlotMatching v hP hT).source (outerLabel v g hg r)).2.val)
      (((rawSlotMatching v hP hT).source (image.labels l)).1.val,((rawSlotMatching v hP hT).source (image.labels l)).2.val) := by
  obtain ⟨e,hc⟩:=PhysicalTiles.wire_code ha
  obtain ⟨_,hflow,hphase,hstraight⟩:=gate_wire_contract v hP hT g hg r p e a hc hn
  have hs:=GateWireGeometry.source_step (refinePoint g.point) (p.1.val,p.2.val) (g.portDirection r)
    ((gateTileState (g,v.2)).incoming.get r) a.2.1 a.1 hstraight hn hflow
  rw [←hphase] at hs
  have hgxy:=outerLabel_source_coordinates v hP hT g hg r
  have hwxy:=wire_source_coordinates v hP hT p a ha ((gateTileState (g,v.2)).incoming.get r)
  change (((rawSlotMatching v hP hT).source (outerLabel v g hg r)).1.val,
    ((rawSlotMatching v hP hT).source (outerLabel v g hg r)).2.val)=
      GateWireGeometry.gatePoint (refinePoint g.point) (FullGateBoundary.endpointPoint (g.portDirection r)
        ((gateTileState (g,v.2)).incoming.get r) (Inventory.initialPhase (gateTileState (g,v.2)) r) false) at hgxy
  change _=PhysicalTiles.wirePoint (p.1.val,p.2.val)
    (GateWireGeometry.wireEndpoint ((gateTileState (g,v.2)).incoming.get r) a.1 a.2.1) at hwxy
  rw [←hgxy,←hwxy] at hs
  have step_order (d : Direction) (x y : ℕ×ℕ) (h : DirectionalStep d x y) : DirectionalOrder d x y := by
    cases d <;> dsimp only [DirectionalStep,DirectionalOrder] at * <;> omega
  exact step_order _ _ _ hs

/-- An outward source incidence enters the first actual box of its adjacent source-edge wire. -/
theorem outgoing_gate_signal (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (p : Raster.Cell v.1)
    (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hn : neighbor (g.portDirection r) (refinePoint g.point)=some (p.1.val,p.2.val))
    (hinc : (g.ports.port r).dir=false)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T)
    (high : OuterHigh (gateImage v hP hT g hg) S r) :
    let image:=tileImage v hP hT (wireIndex v p a ha)
    Catalog.sourceHigh a.1 image.dx image.dy (S.position (image.labels (firstLabel a.1))) := by
  let image:=tileImage v hP hT (wireIndex v p a ha)
  have hi : (gateTileState (g,v.2)).incoming.get r=false:=by rw [gateTileState_incoming]; exact hinc
  obtain ⟨e,hcode⟩:=PhysicalTiles.wire_code ha
  obtain ⟨_,hflow,_,hstraight⟩:=gate_wire_contract v hP hT g hg r p e a hcode hn
  have hc:=gate_wire_source_component v hP hT g hg r p a ha hn
  have ho:=gate_wire_source_order v hP hT g hg r p a ha hn
  simp only [hi,Bool.false_eq_true,ite_false] at hc ho hflow
  have gap:=directional_gap (g.portDirection r) hs (certificate v hP hT)
    (outerLabel v g hg r) (image.labels (firstLabel a.1)) hc ho
  have hh:=(outerHigh_iff v hP hT g hg S r).mp high
  change TravelHigh (g.portDirection r)
    (GateWireGeometry.gatePoint (refinePoint g.point) (FullGateBoundary.endpointPoint (g.portDirection r)
      ((gateTileState (g,v.2)).incoming.get r) true false)) _ at hh
  rw [hi] at hh
  have step:=GateWireGeometry.source_step (refinePoint g.point) (p.1.val,p.2.val)
    (g.portDirection r) false true a.1 hstraight hn hflow
  have result:=travelHigh_join (g.portDirection r) _ _ _ _ step gap hh
  apply (sourceHigh_travel image _).mpr
  change sourceDirection a.1=g.portDirection r at hflow
  rw [hflow]
  exact result

/-- An inward destination incidence excludes the last actual box signal of its adjacent source-edge wire. -/
theorem incoming_gate_exclusive (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3) (p : Raster.Cell v.1)
    (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hn : neighbor (g.portDirection r) (refinePoint g.point)=some (p.1.val,p.2.val))
    (hinc : (g.ports.port r).dir=true)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T)
    (high : OuterHigh (gateImage v hP hT g hg) S r) :
    let image:=tileImage v hP hT (wireIndex v p a ha)
    ¬Catalog.targetHigh a.1 image.dx image.dy (S.position (image.labels (lastLabel a.1))) := by
  let image:=tileImage v hP hT (wireIndex v p a ha)
  have hi : (gateTileState (g,v.2)).incoming.get r=true:=by rw [gateTileState_incoming]; exact hinc
  obtain ⟨e,hcode⟩:=PhysicalTiles.wire_code ha
  obtain ⟨_,hflow,_,hstraight⟩:=gate_wire_contract v hP hT g hg r p e a hcode hn
  have hc:=gate_wire_source_component v hP hT g hg r p a ha hn
  have ho:=gate_wire_source_order v hP hT g hg r p a ha hn
  simp only [hi,ite_true] at hc ho hflow
  have gap:=directional_gap (g.portDirection r) hs (certificate v hP hT)
    (outerLabel v g hg r) (image.labels (lastLabel a.1)) hc ho
  have hh:=(outerHigh_iff v hP hT g hg S r).mp high
  change TravelHigh (g.portDirection r)
    (GateWireGeometry.gatePoint (refinePoint g.point) (FullGateBoundary.endpointPoint (g.portDirection r)
      ((gateTileState (g,v.2)).incoming.get r) true false)) _ at hh
  rw [hi] at hh
  change ¬Catalog.targetHigh a.1 image.dx image.dy (S.position (image.labels (lastLabel a.1)))
  intro hw
  have ht:=(targetHigh_travel image _).mp hw
  change targetDirection a.1=(g.portDirection r).opposite at hflow
  rw [hflow] at ht
  exact GateWireGeometry.incoming_exclusive (refinePoint g.point) (p.1.val,p.2.val)
    (g.portDirection r) a.1 hstraight hn hflow _ _ gap hh ht

end PushPuzzle.PushFS.Reduction.PhysicalInventory

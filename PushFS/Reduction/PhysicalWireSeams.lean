/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalWireSignals
public import PushFS.Reduction.PhysicalWireSeamGeometry
public import PushFS.Gadgets.Wires.Catalog.EndpointComponents
public import PushFS.Gadgets.Wires.Catalog.TravelEndpoints

/-! Actual consecutive ordinary macrocells preserve the real source SCC, gap and directional endpoint signal. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PhysicalBitmap Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem wireImage_point (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) (q : Catalog.Cell) :
    let image:=tileImage v hP hT (wireIndex v p a ha)
    ((image.point q).1.val,(image.point q).2.val)=PhysicalTiles.wirePoint (p.1.val,p.2.val) q := rfl

theorem wire_source_coordinates (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p : Raster.Cell v.1) (a : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a)) (last : Bool) :
    let image:=tileImage v hP hT (wireIndex v p a ha)
    let label:=if last then Catalog.lastLabel a.1 else Catalog.firstLabel a.1
    (((rawSlotMatching v hP hT).source (image.labels label)).1.val,
      ((rawSlotMatching v hP hT).source (image.labels label)).2.val)=
      PhysicalTiles.wirePoint (p.1.val,p.2.val) (if last then lastPoint a.1 a.2.1 else firstPoint a.1 a.2.1) := by
  let image:=tileImage v hP hT (wireIndex v p a ha)
  cases last
  · have he:=(image.sources (firstLabel a.1)).trans (congrArg image.point (source_first a.1 a.2.1 a.2.2))
    exact (congrArg (fun p=>(p.1.val,p.2.val)) he).trans (wireImage_point v hP hT p a ha _)
  · have he:=(image.sources (lastLabel a.1)).trans (congrArg image.point (source_last a.1 a.2.1 a.2.2))
    exact (congrArg (fun p=>(p.1.val,p.2.val)) he).trans (wireImage_point v hP hT p a ha _)

private theorem wire_seam_component (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (p r : Raster.Cell v.1) (a b : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hb : PhysicalTiles.key (CellPlan.cell (v,(r.1.val,r.2.val)))=some (.inr b))
    (hn : neighbor (Catalog.targetDirection a.1) (p.1.val,p.2.val)=some (r.1.val,r.2.val))
    (hd : Catalog.sourceDirection b.1=Catalog.targetDirection a.1) :
    let left:=tileImage v hP hT (wireIndex v p a ha)
    let right:=tileImage v hP hT (wireIndex v r b hb)
    component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source (left.labels (lastLabel a.1)))=
      component (puzzle v hP hT).board ((rawSlotMatching v hP hT).source (right.labels (firstLabel b.1))) := by
  let left:=tileImage v hP hT (wireIndex v p a ha)
  let right:=tileImage v hP hT (wireIndex v r b hb)
  have hc:=last_to_face a.1 a.2.1 a.2.2 a.2.1
  have ht : SameComponent (puzzle v hP hT).board (left.point (lastPoint a.1 a.2.1))
      (left.point (faceCell (targetFace a.1) (2,10))) :=
    ⟨GridEmbedding.staticReach left.walls hc.1,GridEmbedding.staticReach left.walls hc.2⟩
  have hnext : @SameComponent Catalog.width Catalog.height (Catalog.puzzle b.1 b.2.1 b.2.2).board
      (firstPoint b.1 false) (firstPoint b.1 b.2.1) := endpoint_component b.1 b.2.1 b.2.2 false b.2.1 false
  have hnext' : SameComponent (puzzle v hP hT).board (right.point (firstPoint b.1 false))
      (right.point (firstPoint b.1 b.2.1)) :=
    ⟨GridEmbedding.staticReach right.walls hnext.1,GridEmbedding.staticReach right.walls hnext.2⟩
  have he : left.point (faceCell (targetFace a.1) (2,10))=right.point (firstPoint b.1 false) := by
    have hxy:=PhysicalTiles.wire_seam_ghost (p.1.val,p.2.val) (r.1.val,r.2.val) a.1 b.1 hn hd
    apply Prod.ext <;> apply Fin.ext
    · exact congrArg Prod.fst hxy
    · exact congrArg Prod.snd hxy
  rw [he] at ht
  have hsL:=(left.sources (lastLabel a.1)).trans (congrArg left.point (source_last a.1 a.2.1 a.2.2))
  have hsR:=(right.sources (firstLabel b.1)).trans (congrArg right.point (source_first b.1 b.2.1 b.2.2))
  apply component_eq_iff.mpr
  exact hsL.symm ▸hsR.symm ▸⟨ht.1.trans hnext'.1,hnext'.2.trans ht.2⟩

theorem wire_seam_signal (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (p r : Raster.Cell v.1) (a b : Catalog.Bitmap.Args)
    (ha : PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a))
    (hb : PhysicalTiles.key (CellPlan.cell (v,(r.1.val,r.2.val)))=some (.inr b))
    (hn : neighbor (Catalog.targetDirection a.1) (p.1.val,p.2.val)=some (r.1.val,r.2.val))
    (hd : Catalog.sourceDirection b.1=Catalog.targetDirection a.1)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) (cert : Certificate (puzzle v hP hT)) :
    let left:=tileImage v hP hT (wireIndex v p a ha)
    let right:=tileImage v hP hT (wireIndex v r b hb)
    Catalog.targetHigh a.1 left.dx left.dy (S.position (left.labels (lastLabel a.1)))→
      Catalog.sourceHigh b.1 right.dx right.dy (S.position (right.labels (firstLabel b.1))) := by
  let left:=tileImage v hP hT (wireIndex v p a ha)
  let right:=tileImage v hP hT (wireIndex v r b hb)
  dsimp only
  intro hin
  have hl:=wire_source_coordinates v hP hT p a ha true
  have hr:=wire_source_coordinates v hP hT r b hb false
  have ho:=PhysicalTiles.wire_seam_order (p.1.val,p.2.val) (r.1.val,r.2.val) a.1 b.1 a.2.1 b.2.1 hn hd
  have horder : DirectionalOrder (targetDirection a.1)
      (((rawSlotMatching v hP hT).source (left.labels (lastLabel a.1))).1.val,
        ((rawSlotMatching v hP hT).source (left.labels (lastLabel a.1))).2.val)
      (((rawSlotMatching v hP hT).source (right.labels (firstLabel b.1))).1.val,
        ((rawSlotMatching v hP hT).source (right.labels (firstLabel b.1))).2.val) := hl.symm ▸hr.symm ▸ho
  have hgap:=directional_gap (targetDirection a.1) hs cert (left.labels (lastLabel a.1))
    (right.labels (firstLabel b.1)) (wire_seam_component v hP hT p r a b ha hb hn hd) horder
  have hrl:=wireImage_point v hP hT p a ha (lastPoint a.1 true)
  have hrr:=wireImage_point v hP hT r b hb (firstPoint b.1 true)
  have hstep : DirectionalStep (targetDirection a.1)
      ((left.point (lastPoint a.1 true)).1.val,(left.point (lastPoint a.1 true)).2.val)
      ((right.point (firstPoint b.1 true)).1.val,(right.point (firstPoint b.1 true)).2.val) :=
    hrl.symm ▸hrr.symm ▸PhysicalTiles.wire_seam_true_step (p.1.val,p.2.val) (r.1.val,r.2.val) a.1 b.1 hn hd
  have hout:=travelHigh_join (targetDirection a.1) _ _ _ _ hstep hgap ((targetHigh_travel left _).mp hin)
  apply (sourceHigh_travel right _).mpr
  exact hd.symm ▸hout

end PushPuzzle.PushFS.Reduction.PhysicalInventory

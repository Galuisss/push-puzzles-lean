/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingMeshBands
public import PushS.FiniteRoutingInitialFaces

/-! The actual transverse wall thickness at every source port is exactly bounded by `w`. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem line_wall_perpendicular_band (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    Line.PerpendicularBand w (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0)
      ((PrimitiveCode.line c).world w hw p) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hc.2.1]
    exact segment_travels _ hc.1
  change p ∈ (Line.walls w atoms c.above).map (Line.rotation w atoms (segmentDirection c.segment)).cells.toEmbedding at hp
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hp
  have hs := Line.placed_wall_band w atoms c.above (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2 a ha
  rw [←he]
  exact hs

private theorem line_endpoint_wall_band_tight (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    PortBand w w face ((PrimitiveCode.line c).world w hw p) := by
  have hb := line_wall_perpendicular_band w hw c hc p hp
  have ht := segment_travels c.segment hc.1
  rw [hd] at hb
  rw [hd,he] at ht
  cases face <;> dsimp [PortBand,Line.PerpendicularBand,Line.along,Travels,advance,Direction.opposite,boundaryPoint] at * <;> omega

private theorem gate_wall_collar_band_tight (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w w face (c.world w hw p) := by
  obtain ⟨role,rfl,hd⟩ := gate_wall_collar w hw g c hc p hp face hf
  exact line_endpoint_wall_band_tight w hw _ (gatePortLine_good w g role) face (g.incoming.get role)
    ((armSpec_last_direction w g role).trans hd)
    (by simpa only [gatePortLine,←hd] using armSpec_last_finish w g role) p hp

private theorem centered_wall_collar_band_tight (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (hcenter : CenteredLine w c.segment)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face ((PrimitiveCode.line c).world w hw p)) :
    PortBand w w face ((PrimitiveCode.line c).world w hw p) := by
  have hband := line_wall_perpendicular_band w hw c hc p hp
  obtain ⟨u,hu,ha⟩ := line_wall_footprint w hw c hc p hp
  have hb := Segment.coordinate_bounds hu
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> cases face <;> simp only [hd] at ht hband <;>
    dsimp [CenteredLine,PortBand,Line.PerpendicularBand,Line.along,InCollar,Travels,boundaryPoint,Nearby] at * <;>
    simp only [tileStride,spacing,padding] at * <;> omega

private theorem wire_wall_collar_band_tight (w : ℕ) (hw : 2 ≤ w) (q : Gadgets.Wires.Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w w face (c.world w hw p) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact centered_wall_collar_band_tight w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
      (wire_line_centered w q i hi') p hp face hf
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht p)) hf).elim

theorem local_wall_collar_band_tight (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w w face (c.world w hw p) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_wall_collar_band_tight w hw g.2 c hc p hp face hf
    | inr q => exact wire_wall_collar_band_tight w hw q.2 c hc p hp face hf

end PushPuzzle.PushS.FiniteRouting

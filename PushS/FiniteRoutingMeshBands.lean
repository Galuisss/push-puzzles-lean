/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateCollars
public import PushS.FiniteRoutingWireCollars
public import PushS.FiniteSourceInventory

/-! Actual walls meet a coarse-cell edge only inside its literal narrow central port band. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

/-- The transverse width bound at a macrocell port. -/
@[expose] def PortBand (w margin : ℕ) (face : Direction) (a : ℕ × ℕ) : Prop :=
  match face with
  | .north | .south => padding w+25*spacing w ≤ a.1+margin ∧ a.1 ≤ padding w+25*spacing w+margin
  | .east | .west => padding w+25*spacing w ≤ a.2+margin ∧ a.2 ≤ padding w+25*spacing w+margin

private theorem line_endpoint_wall_band (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    PortBand w (w+1) face ((PrimitiveCode.line c).world w hw p) := by
  obtain ⟨u,hu,hnear⟩ := line_wall_footprint w hw c hc p hp
  have hb := Segment.coordinate_bounds hu
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  rw [he] at hb
  cases face <;> dsimp [PortBand,Travels,advance,Direction.opposite,boundaryPoint,Nearby] at * <;> omega

private theorem gate_wall_collar_band (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w (w+1) face (c.world w hw p) := by
  obtain ⟨role,rfl,hd⟩ := gate_wall_collar w hw g c hc p hp face hf
  exact line_endpoint_wall_band w hw _ (gatePortLine_good w g role) face (g.incoming.get role)
    ((armSpec_last_direction w g role).trans hd)
    (by simpa only [gatePortLine,←hd] using armSpec_last_finish w g role) p hp

private theorem centered_wall_collar_band (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (hcenter : CenteredLine w c.segment)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face ((PrimitiveCode.line c).world w hw p)) :
    PortBand w (w+1) face ((PrimitiveCode.line c).world w hw p) := by
  obtain ⟨u,hu,ha⟩ := line_wall_footprint w hw c hc p hp
  have hb := Segment.coordinate_bounds hu
  have ht := segment_travels c.segment hc.1
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> cases face <;> simp only [hd] at ht <;>
    dsimp [CenteredLine,PortBand,Line.along,InCollar,Travels,boundaryPoint,Nearby] at * <;>
    simp only [tileStride,spacing,padding] at * <;> omega

private theorem wire_wall_collar_band (w : ℕ) (hw : 2 ≤ w) (q : Gadgets.Wires.Catalog.Bitmap.Args) (c : PrimitiveCode)
    (hc : c ∈ wireCodes w q) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w (w+1) face (c.world w hw p) := by
  change c ∈ (wireSpec w q).codes at hc
  obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w q).mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
  · exact centered_wall_collar_band w hw _ ((wireSpec w q).line_good w (wireSpec_geometry w q) i hi')
      (wire_line_centered w q i hi') p hp face hf
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw q i ht p)) hf).elim

theorem local_wall_collar_band (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : PrimitiveCode)
    (hc : c ∈ FiniteSourceInventory.localCodes w code) (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) : PortBand w (w+1) face (c.world w hw p) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_wall_collar_band w hw g.2 c hc p hp face hf
    | inr q => exact wire_wall_collar_band w hw q.2 c hc p hp face hf

end PushPuzzle.PushS.FiniteRouting

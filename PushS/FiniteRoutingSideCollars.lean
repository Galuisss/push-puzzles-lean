/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSideStock
public import PushS.FiniteRoutingPortBounds

/-! Exposed line-side marks in a source collar avoid its literal normal-stock axis. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem endpoint_off_axis (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    {a : ℕ × ℕ} (ha : ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0) a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a := by
  have hb := line_endpoint_row_lane w hw c hc face incoming hd he 0 (Nat.zero_le _)
  rw [LineCode.rowWorld_eq,hd] at hb
  rw [hd] at ha
  cases face <;> dsimp [SameLane] at ha hb ⊢ <;> omega

private theorem gate_off_axis_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : .line c ∈ gateCodes w g) {a : ℕ × ℕ}
    (hp : c.NearTrace w a) (ha : ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0) a) (face : Direction) (hf : InCollar w face a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi hp
  by_cases hn : i+1 < (armRoute w g role).length
  · exact ((interior_not_collar w face (nearby_interior w (w+2) (by unfold padding; omega)
      (armRoute_nonlast_interior w g role i hn hu) hu')) hf).elim
  · have he : i = (armRoute w g role).length-1 := by omega
    subst i
    have hd := arm_last_collar_face w g role face (w+2) (by unfold padding; omega) hu hu' hf
    apply endpoint_off_axis w hw _ (gatePortLine_good w g role) face (g.incoming.get role)
      ((armSpec_last_direction w g role).trans hd) _ ha
    simpa only [gatePortLine,←hd] using armSpec_last_finish w g role

private theorem wire_off_axis_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (q : Gadgets.Wires.Catalog.Bitmap.Args)
    (c : LineCode) (hc : .line c ∈ wireCodes w q) {a : ℕ × ℕ}
    (hp : c.NearTrace w a) (ha : ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0) a) (face : Direction) (hf : InCollar w face a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w q).line_code_origin c hc
  let P := wireSpec w q
  have G : P.Geometry w := wireSpec_geometry w q
  obtain ⟨u,hu,hu'⟩ := P.side_at w G i hi hp
  rcases wire_point_collar_location w q.1 i hi face (w+2) (by unfold padding; omega) hu hu' hf with h | h
  · rcases h with ⟨rfl,rfl⟩
    have hn := ha
    rw [wire_first_direction,wire_first_start] at hn
    cases hd : Gadgets.Wires.Catalog.sourceDirection q.1 <;>
      simp only [hd] at hn ⊢ <;> dsimp [SameLane,Line.along,Direction.opposite,boundaryPoint] at hn ⊢ <;> omega
  · apply endpoint_off_axis w hw _ (P.line_good w G i hi) face false
      ((wire_last_direction w q i h.1).trans h.2.symm) _ ha
    simpa only [Bool.toNat_false,advance_zero,←h.2] using wire_last_finish w q i h.1

theorem local_off_axis_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) {a : ℕ × ℕ}
    (hp : c.NearTrace w a) (ha : ¬SameLane (segmentDirection c.segment) (Line.along w (segmentDirection c.segment) c.segment.start 0) a) (face : Direction) (hf : InCollar w face a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a := by
  exact localCodes_elim hc
    (fun g hg => gate_off_axis_collar_off_lane w hw g.2 c hg hp ha face hf)
    (fun q hq => wire_off_axis_collar_off_lane w hw q.2 c hq hp ha face hf)

theorem local_side_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) {a : ℕ × ℕ}
    (hp : c.NearTrace w a) (ha : SideBand w c a) (face : Direction) (hf : InCollar w face a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a :=
  local_off_axis_collar_off_lane w hw code c hc hp ha.2.2 face hf

end PushPuzzle.PushS.FiniteRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingOuterLanes
public import PushS.FiniteRoutingActionLocal
public import PushS.FiniteRoutingMeshBandsTight
public import PushS.FiniteRoutingPortBounds
public import PushS.FiniteRoutingBandContacts

/-! Exposed outer lanes lie one cell beyond the transverse wall bands at every macrocell seam. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side FiniteGeometry.side

/-- Either exposed lane at transverse distance `w+1` from the central source port. -/
@[expose] def PortLaneOuter (w : ℕ) (face : Direction) (a : ℕ × ℕ) : Prop :=
  match face with
  | .north | .south => a.1+(w+1) = padding w+25*spacing w ∨ a.1 = padding w+25*spacing w+(w+1)
  | .east | .west => a.2+(w+1) = padding w+25*spacing w ∨ a.2 = padding w+25*spacing w+(w+1)

private theorem PortLaneOuter.band {w : ℕ} {face : Direction} {a : ℕ × ℕ}
    (h : PortLaneOuter w face a) : PortBand w (w+1) face a := by
  cases face <;> dsimp [PortLaneOuter,PortBand] at * <;> omega

private theorem macroShift_injective (w : ℕ) (p : ℕ × ℕ) : Function.Injective (macroShift w p) := by
  intro a b he
  exact Prod.ext (Nat.add_left_cancel (congrArg Prod.fst he)) (Nat.add_left_cancel (congrArg Prod.snd he))

theorem macro_outer_wall_ne (w : ℕ) (p r a b : ℕ × ℕ)
    (ha : a.1 < tileSide w ∧ a.2 < tileSide w) (hb : b.1 < tileSide w ∧ b.2 < tileSide w)
    (houter : ∀ face, InCollar w face a → PortLaneOuter w face a)
    (hwall : ∀ face, InCollar w face b → PortBand w w face b)
    (hlocal : p = r → a ≠ b) : macroShift w p a ≠ macroShift w r b := by
  intro he
  by_cases hp : p = r
  · subst r
    exact hlocal rfl (macroShift_injective w p he)
  · obtain ⟨d,hn,hda,hdb⟩ := macro_band_contact w (w+1) (by unfold padding; omega) p r a b ha hb
      (fun face hf => PortLaneOuter.band (houter face hf)) hp he
    have ht := neighbor_travels hn
    have ho := houter d hda
    have hw := hwall d.opposite hdb
    obtain ⟨hx,hy⟩ := (macroShift_eq_iff w p r a b).mp he
    cases d <;> dsimp [Travels] at ht <;> dsimp [PortLaneOuter,PortBand,Direction.opposite] at ho hw
    all_goals first | rw [ht.1] at hx | rw [ht.1] at hy
    all_goals omega

namespace LineCode

theorem outerCell_active (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (north : Bool)
    (x : Fin (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))))
    (hx : FiniteTools.radius w+1 ≤ x.val)
    (hx' : x.val ≤ FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) :
    Line.outerCell w _ north x ∈ Line.Action.active w _ c.above c.last :=
  (FiniteWireFrame.floor_iff _ _ _).mp (Line.Action.outer_macro_free (last:=c.last) w hw 0 _ c.above north x hx hx').1

theorem laneWorld_actionWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (north : Bool) (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    c.laneWorld w hw hc north n hn = c.actionWorld w hw
      (Line.outerCell w _ north ⟨FiniteTools.radius w+n,by
        have hs := Line.program_span_of_bound w (segmentLength c.segment) (c.above != c.desiredSide) hc.2.1
        unfold Line.width FiniteTools.radius
        omega⟩) := rfl

private theorem lane_endpoint_outer (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (north : Bool) (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    PortLaneOuter w face (c.laneWorld w hw hc north n hn) := by
  rw [laneWorld_eq,hd]
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  cases face <;> cases north <;>
    dsimp [PortLaneOuter,Line.outerAlong,Travels,advance,Direction.opposite,boundaryPoint] at * <;>
    simp only [padding,spacing,tileStride] at * <;> omega

private theorem lane_start_outer (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (face : Direction) (hd : segmentDirection c.segment = face.opposite)
    (he : c.segment.start = boundaryPoint w face)
    (north : Bool) (n : ℕ) (hn : n ≤ segmentLength c.segment+1) :
    PortLaneOuter w face (c.laneWorld w hw hc north n hn) := by
  rw [laneWorld_eq,hd,he]
  cases face <;> cases north <;>
    dsimp [PortLaneOuter,Line.outerAlong,Direction.opposite,boundaryPoint] at * <;>
    simp only [padding,spacing,tileStride,or_true] at * <;> omega

end LineCode

private theorem PathSpec.lane_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length) (hgood : LineGood w (P.line i).segment)
    (north : Bool) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ segmentLength (P.line i).segment) :
    ∃ u, (segmentAt P.segments i).Contains u ∧
      Nearby (w+2) ((P.line i).laneWorld w hw hgood north n (by omega)) (padding w+u.1,padding w+u.2) := by
  let x : Fin (Line.width w (Line.program w (segmentLength (P.line i).segment) ((P.line i).above != (P.line i).desiredSide))) :=
    ⟨FiniteTools.radius w+n,by
      have hs := Line.program_span_of_bound w (segmentLength (P.line i).segment) ((P.line i).above != (P.line i).desiredSide) hgood.2.1
      unfold Line.width FiniteTools.radius
      omega⟩
  have hs := Line.program_span_of_bound w (segmentLength (P.line i).segment) ((P.line i).above != (P.line i).desiredSide) hgood.2.1
  have hp := (P.line i).outerCell_active w hw north x (by dsimp only [x]; omega) (by dsimp only [x]; omega)
  obtain ⟨u,hu,ha⟩ := P.action_at w hw G i hi (Line.outerCell w _ north x) hp
  have he : (P.line i).actionWorld w hw (Line.outerCell w _ north x) =
      (P.line i).laneWorld w hw hgood north n (by omega) := rfl
  exact ⟨u,hu,he ▸ ha⟩

theorem gate_lane_collar_outer (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ gateCodes w g) (hgood : LineGood w c.segment)
    (north : Bool) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ segmentLength c.segment)
    (face : Direction) (hf : InCollar w face (c.laneWorld w hw hgood north n (by omega))) :
    PortLaneOuter w face (c.laneWorld w hw hgood north n (by omega)) := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  let P := armSpec w g role
  obtain ⟨u,hu,ha⟩ := P.lane_at w hw (armSpec_geometry w g role) i hi hgood north n hn0 hn
  by_cases hlast : i+1 < (armRoute w g role).length
  · exact ((interior_not_collar w face (nearby_interior w (w+2) (by unfold padding; omega)
      (armRoute_nonlast_interior w g role i hlast hu) ha)) hf).elim
  · have hi' : i = (armRoute w g role).length-1 := by change i < (armRoute w g role).length at hi; omega
    subst i
    have hd := arm_last_collar_face w g role face (w+2) (by unfold padding; omega) hu ha hf
    apply LineCode.lane_endpoint_outer w hw _ hgood face (g.incoming.get role) _ _ north n (by omega)
    · exact (armSpec_last_direction w g role).trans hd
    · simpa only [P,←hd] using armSpec_last_finish w g role

private theorem wire_lane_collar_outer (w : ℕ) (hw : 2 ≤ w) (a : Catalog.Bitmap.Args) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ wireCodes w a) (hgood : LineGood w c.segment)
    (north : Bool) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ segmentLength c.segment)
    (face : Direction) (hf : InCollar w face (c.laneWorld w hw hgood north n (by omega))) :
    PortLaneOuter w face (c.laneWorld w hw hgood north n (by omega)) := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w a).line_code_origin c hc
  let P := wireSpec w a
  obtain ⟨u,hu,ha⟩ := P.lane_at w hw (wireSpec_geometry w a) i hi hgood north n hn0 hn
  rcases wire_point_collar_location w a.1 i hi face (w+2) (by unfold padding; omega) hu ha hf with h | h
  · rcases h with ⟨rfl,rfl⟩
    apply LineCode.lane_start_outer w hw _ hgood _ _ (wire_first_start w a) north n (by omega)
    simpa only [Direction.opposite_opposite] using wire_first_direction w a
  · rcases h with ⟨hlast,rfl⟩
    apply LineCode.lane_endpoint_outer w hw _ hgood _ false (wire_last_direction w a i hlast) _ north n (by omega)
    simpa only [Bool.toNat_false,advance_zero] using wire_last_finish w a i hlast

theorem local_lane_collar_outer (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ FiniteSourceInventory.localCodes w code) (hgood : LineGood w c.segment)
    (north : Bool) (n : ℕ) (hn0 : 1 ≤ n) (hn : n ≤ segmentLength c.segment)
    (face : Direction) (hf : InCollar w face (c.laneWorld w hw hgood north n (by omega))) :
    PortLaneOuter w face (c.laneWorld w hw hgood north n (by omega)) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_lane_collar_outer w hw g.2 c hc hgood north n hn0 hn face hf
    | inr a => exact wire_lane_collar_outer w hw a.2 c hc hgood north n hn0 hn face hf

end PushPuzzle.PushS.FiniteRouting

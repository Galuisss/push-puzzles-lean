/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionLocal
public import PushS.FiniteRoutingPortBounds

/-! Literal line endpoints and guard sides at every used source port. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction Gadgets.Wires

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side FiniteGeometry.side

/-- The literal endpoint, ownership and guard side of a source-boundary line. -/
@[expose] def LinePort (w : ℕ) (c : LineCode) (face : Direction) (incoming : Bool) : Prop :=
  (segmentDirection c.segment = face ∧
    c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat ∧
    c.last = !incoming ∧ c.desiredSide = incoming) ∨
  (incoming = true ∧ segmentDirection c.segment = face.opposite ∧
    c.segment.start = boundaryPoint w face ∧ c.above = false)

theorem gatePortLine_port (w : ℕ) (g : GateTileState) (role : Fin 3) :
    LinePort w (gatePortLine w g role) (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) (g.incoming.get role) := by
  refine Or.inl ⟨armSpec_last_direction w g role,armSpec_last_finish w g role,gatePortLine_last w g role,?_⟩
  have hi : (armRoute w g role).length-1+1 = (armRoute w g role).length := by rw [armRoute_length,route_length]; omega
  simp only [gatePortLine,PathSpec.line,lineCodeAt,finalSide,armSpec,hi,ite_true]

private theorem wire_first_port (w : ℕ) (a : Catalog.Bitmap.Args) :
    LinePort w ((wireSpec w a).line 0) (Catalog.sourceDirection a.1).opposite true := by
  refine Or.inr ⟨rfl,?_,wire_first_start w a,rfl⟩
  simpa only [Direction.opposite_opposite] using wire_first_direction w a

theorem wire_last_port (w : ℕ) (a : Catalog.Bitmap.Args) (i : ℕ) (hi : i+1 = (wireRoute w a.1).length) :
    LinePort w ((wireSpec w a).line i) (Catalog.targetDirection a.1) false := by
  refine Or.inl ⟨wire_last_direction w a i hi,?_,?_,?_⟩
  · simpa only [Bool.toNat_false,advance_zero] using wire_last_finish w a i hi
  · simp only [wireSpec,PathSpec.line,lineCodeAt,ownsLast,hi,ite_true,Bool.not_false]
  · simp only [wireSpec,PathSpec.line,lineCodeAt,finalSide,hi,ite_true]

private theorem gate_action_collar (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ gateCodes w g) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (face : Direction) (hf : InCollar w face (c.actionWorld w hw p)) :
    ∃ role : Fin 3, c = gatePortLine w g role ∧ PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face := by
  obtain ⟨role,i,hi,rfl⟩ := gate_line_origin w g c hc
  obtain ⟨u,hu,ha⟩ := (armSpec w g role).action_at w hw (armSpec_geometry w g role) i hi p hp
  by_cases hlast : i+1 < (armRoute w g role).length
  · exact ((interior_not_collar w face (nearby_interior w (w+2) (by unfold padding; omega)
      (armRoute_nonlast_interior w g role i hlast hu) ha)) hf).elim
  · have he : i = (armRoute w g role).length-1 := by omega
    subst i
    exact ⟨role,rfl,arm_last_collar_face w g role face (w+2) (by unfold padding; omega) hu ha hf⟩

private theorem gate_action_collar_port (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (vertex : Plan.VertexData) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ gateCodes w g) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (face : Direction) (hf : InCollar w face (c.actionWorld w hw p)) :
    ∃ incoming, LocalPort (some (.inl (vertex,g))) face incoming ∧ LinePort w c face incoming := by
  obtain ⟨role,rfl,hd⟩ := gate_action_collar w hw g c hc p hp face hf
  refine ⟨g.incoming.get role,⟨role,hd,rfl⟩,?_⟩
  simpa only [hd] using gatePortLine_port w g role

private theorem wire_action_collar_port (w : ℕ) (hw : 2 ≤ w) (a : Catalog.Bitmap.Args) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ wireCodes w a) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (face : Direction) (hf : InCollar w face (c.actionWorld w hw p)) :
    ∃ incoming, LocalPort (some (.inr (0,a))) face incoming ∧ LinePort w c face incoming := by
  obtain ⟨i,hi,rfl⟩ := (wireSpec w a).line_code_origin c hc
  obtain ⟨u,hu,ha⟩ := (wireSpec w a).action_at w hw (wireSpec_geometry w a) i hi p hp
  rcases wire_point_collar_location w a.1 i hi face (w+2) (by unfold padding; omega) hu ha hf with h | h
  · rcases h with ⟨rfl,rfl⟩
    exact ⟨true,Or.inl ⟨rfl,rfl⟩,wire_first_port w a⟩
  · rcases h with ⟨hlast,rfl⟩
    exact ⟨false,Or.inr ⟨rfl,rfl⟩,wire_last_port w a i hlast⟩

theorem local_action_collar_port (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : PrimitiveCode.line c ∈ FiniteSourceInventory.localCodes w code) (p : c.ActionCell w)
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (face : Direction) (hf : InCollar w face (c.actionWorld w hw p)) :
    ∃ incoming, LocalPort code face incoming ∧ LinePort w c face incoming := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_action_collar_port w hw g.2 g.1 c hc p hp face hf
    | inr a => exact wire_action_collar_port w hw a.2 c hc p hp face hf

private theorem gate_wall_collar_port (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (vertex : Plan.VertexData) (d : PrimitiveCode)
    (hd : d ∈ gateCodes w g) (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height)
    (hq : q ∈ (d.instanceOf w hw).board.walls) (face : Direction) (hf : InCollar w face (d.world w hw q)) :
    ∃ c incoming, d = .line c ∧ LocalPort (some (.inl (vertex,g))) face incoming ∧ LinePort w c face incoming := by
  obtain ⟨role,rfl,he⟩ := gate_wall_collar w hw g d hd q hq face hf
  refine ⟨gatePortLine w g role,g.incoming.get role,rfl,⟨role,he,rfl⟩,?_⟩
  simpa only [he] using gatePortLine_port w g role

private theorem wire_wall_collar_port (w : ℕ) (hw : 2 ≤ w) (a : Catalog.Bitmap.Args) (d : PrimitiveCode)
    (hd : d ∈ wireCodes w a) (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height)
    (hq : q ∈ (d.instanceOf w hw).board.walls) (face : Direction) (hf : InCollar w face (d.world w hw q)) :
    ∃ c incoming, d = .line c ∧ LocalPort (some (.inr (0,a))) face incoming ∧ LinePort w c face incoming := by
  change d ∈ (wireSpec w a).codes at hd
  obtain ⟨i,hi,hd⟩ := List.mem_flatMap.mp hd
  have hi' := List.mem_range.mp hi
  rcases ((wireSpec w a).mem_block i d).mp hd with rfl | ⟨ht,rfl⟩
  · obtain ⟨u,hu,ha⟩ := (wireSpec w a).line_wall_at w hw (wireSpec_geometry w a) i hi' q hq
    rcases wire_point_collar_location w a.1 i hi' face (w+1) (by unfold padding; omega) hu ha hf with h | h
    · rcases h with ⟨rfl,rfl⟩
      exact ⟨_,true,rfl,Or.inl ⟨rfl,rfl⟩,wire_first_port w a⟩
    · rcases h with ⟨hlast,rfl⟩
      exact ⟨_,false,rfl,Or.inr ⟨rfl,rfl⟩,wire_last_port w a i hlast⟩
  · exact ((interior_not_collar w face (wire_turn_window_interior w hw a i ht q)) hf).elim

theorem local_wall_collar_line_port (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (d : PrimitiveCode)
    (hd : d ∈ FiniteSourceInventory.localCodes w code) (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height)
    (hq : q ∈ (d.instanceOf w hw).board.walls) (face : Direction) (hf : InCollar w face (d.world w hw q)) :
    ∃ c incoming, d = .line c ∧ LocalPort code face incoming ∧ LinePort w c face incoming := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hd
  | some code =>
    cases code with
    | inl g => exact gate_wall_collar_port w hw g.2 g.1 d hd q hq face hf
    | inr a => exact wire_wall_collar_port w hw a.2 d hd q hq face hf

end PushPuzzle.PushS.FiniteRouting

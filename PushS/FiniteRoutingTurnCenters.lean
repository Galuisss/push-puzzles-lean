/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingGateRows

/-! The actual corner center of every emitted turn avoids the complete path wall union. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls FiniteGeometry.side

theorem Line.along_zero (w : ℕ) (d : Direction) (p : ℕ × ℕ) :
    Line.along w d p 0 = (padding w+p.1,padding w+p.2) := by cases d <;> simp [Line.along]

namespace PathSpec

private theorem center_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (i : ℕ) :
    Nearby 0 ((P.turn i).centerWorld w hw)
      (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) := by
  rw [TurnCode.centerWorld_eq]
  change Nearby 0 (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) _
  unfold Nearby
  omega

private theorem center_line_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (p : Cell ((PrimitiveCode.line (P.line i)).instanceOf w hw).width ((PrimitiveCode.line (P.line i)).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line (P.line i)).instanceOf w hw).board.walls) :
    (P.turn j).centerWorld w hw ≠ (PrimitiveCode.line (P.line i)).world w hw p := by
  have H := P.junction_contract w G j hj
  by_cases he : i = j
  · subst i
    rw [TurnCode.centerWorld_eq,←Line.along_zero w (P.turn j).outgoing]
    exact outgoing_ray_ne_incoming_wall w hw _ _ H.incoming_good H.perpendicular
      H.incoming_direction H.incoming_finish 0 p hp
  by_cases he : i = j+1
  · subst i
    rw [TurnCode.centerWorld_eq,←Line.along_zero w (P.turn j).incoming.opposite]
    exact incoming_ray_ne_outgoing_wall w hw _ _ H.outgoing_good H.perpendicular
      H.outgoing_direction H.outgoing_start 0 p hp
  by_cases hij : i < j
  · obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G i hi p hp
    have hb := P.center_at w hw j
    rw [P.join_eq w G j hj.1] at hb
    exact Ne.symm (P.marks_ne w G i (j+1) hi hj.1 (by omega) (w+1) 0
      (by unfold FiniteGeometry.origin; omega) hu (P.start_contains w G (j+1) hj.1) ha hb)
  · obtain ⟨v,hv,hb⟩ := P.line_wall_at w hw G i hi p hp
    exact P.marks_ne w G j i (by omega) hi (by omega) 0 (w+1)
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G j (by omega)) hv (P.center_at w hw j) hb

private theorem center_turn_wall_ne (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (P.turn i).centerWorld w hw ≠ (PrimitiveCode.turn (P.turn j)).world w hw p := by
  have hil := hi.1
  have hjl := hj.1
  rcases lt_trichotomy i j with hij | hij | hij
  · have hb := P.turn_wall_at w hw j p
    rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) (by omega) hj.1 (by omega) 0 (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G i (by omega))
      (P.start_contains w G (j+1) hj.1) (P.center_at w hw i) hb
  · subst j
    rw [TurnCode.centerWorld_eq,←Line.along_zero w (P.turn i).outgoing]
    exact Ne.symm (turn_wall_ne_ray w hw (P.turn i) (P.turn_perpendicular w G i hi) false 0 p hp)
  · have hb := P.center_at w hw i
    rw [P.join_eq w G i hi.1] at hb
    exact Ne.symm (P.marks_ne w G j (i+1) (by omega) hi.1 (by omega) (FiniteTools.radius w) 0
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega) (P.finish_contains w G j (by omega))
      (P.start_contains w G (i+1) hi.1) (P.turn_wall_at w hw j p) hb)

private theorem center_codes_wall_clear (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (c : PrimitiveCode) (hc : c ∈ P.codes)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hp : p ∈ (c.instanceOf w hw).board.walls) :
    (P.turn i).centerWorld w hw ≠ c.world w hw p := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.center_line_wall_ne w hw G j i (List.mem_range.mp hj) hi p hp
  · exact P.center_turn_wall_ne w hw G i j hi ht p hp

theorem turn_code_origin (P : PathSpec) (c : TurnCode) (hc : .turn c ∈ P.codes) :
    ∃ i, P.hasTurn i ∧ c = P.turn i := by
  obtain ⟨i,_,hc⟩ := List.mem_flatMap.mp hc
  rcases (P.mem_block i (.turn c)).mp hc with he | ⟨ht,he⟩
  · cases he
  · exact ⟨i,ht,PrimitiveCode.turn.inj he⟩

end PathSpec

theorem gate_turn_origin (w : ℕ) (g : GateTileState) (c : TurnCode) (hc : .turn c ∈ gateCodes w g) :
    ∃ (role : Fin 3) (i : ℕ), (armSpec w g role).hasTurn i ∧ c = (armSpec w g role).turn i := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with hc | hc
  · cases hc
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    obtain ⟨i,hi,he⟩ := (armSpec w g role).turn_code_origin c hc
    exact ⟨role,i,hi,he⟩

private theorem gate_center_wall_clear (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : TurnCode)
    (hc : .turn c ∈ gateCodes w g) (d : PrimitiveCode) (hd : d ∈ gateCodes w g)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    c.centerWorld w hw ≠ d.world w hw p := by
  obtain ⟨role,i,hi,rfl⟩ := gate_turn_origin w g c hc
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  have ha := P.center_at w hw i
  rw [P.join_eq w G i hi.1] at ha
  have hu := P.start_contains w G (i+1) hi.1
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact core_tail_ne w hw g role 0 (by omega)
      ⟨_,P.segment_mem_tail (i+1) hi.1 (by omega),hu⟩ ha p
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases he : role = other
    · subst other
      exact P.center_codes_wall_clear w hw G i hi d hd p hp
    · rcases (armSpec w g other).code_wall_trace w hw (armSpec_geometry w g other) d hd p hp with h | h
      · obtain ⟨v,hv,hb⟩ := h
        apply footprint_ne (w := w) (m := 0) (n := w+1) _ ha hb
        intro hnear
        exact armRoutes_separated_wide w g he ⟨_,P.segment_mem (i+1) hi.1,hu⟩ hv (nearby_of_le (by omega) hnear)
      · obtain ⟨v,hv,hb⟩ := h
        apply Ne.symm
        apply footprint_ne (w := w) (m := FiniteTools.radius w) (n := 0) _ hb ha
        intro hnear
        exact armRoute_tail_separated w g (Ne.symm he) hv ⟨_,P.segment_mem (i+1) hi.1,hu⟩
          (nearby_of_le (by unfold FiniteTools.radius FiniteGeometry.origin; omega) hnear)

theorem local_center_wall_clear (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : TurnCode)
    (hc : .turn c ∈ FiniteSourceInventory.localCodes w code) (d : PrimitiveCode)
    (hd : d ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hp : p ∈ (d.instanceOf w hw).board.walls) :
    c.centerWorld w hw ≠ d.world w hw p := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g => exact gate_center_wall_clear w hw g.2 c hc d hd p hp
    | inr q =>
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).turn_code_origin c hc
      exact (wireSpec w q.2).center_codes_wall_clear w hw (wireSpec_geometry w q.2) i hi d hd p hp

theorem local_turn_window_interior (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : TurnCode)
    (hc : .turn c ∈ FiniteSourceInventory.localCodes w code) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) :
    TileInterior w ((PrimitiveCode.turn c).world w hw p) := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at hc
  | some code =>
    cases code with
    | inl g =>
      obtain ⟨role,i,hi,rfl⟩ := gate_turn_origin w g.2 c hc
      exact arm_turn_window_interior w hw g.2 role i hi p
    | inr q =>
      obtain ⟨i,hi,rfl⟩ := (wireSpec w q.2).turn_code_origin c hc
      exact wire_turn_window_interior w hw q.2 i hi p

end PushPuzzle.PushS.FiniteRouting

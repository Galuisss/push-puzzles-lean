/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnActionPath
public import PushS.FiniteRoutingWireCollars
public import PushS.FiniteRoutingTurnCenters

/-! Every real turn action avoids the complete wall union of its emitted gate or ordinary tile. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

private theorem different_arms_turn_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState)
    (role other : Fin 3) (hne : role ≠ other) (i : ℕ) (hi : (armSpec w g role).hasTurn i)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (d : PrimitiveCode) (hd : d ∈ (armSpec w g other).codes)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    ((armSpec w g role).turn i).actionWorld w hw p ≠ d.world w hw q := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  have ha := (P.turn i).action_footprint w hw p hp
  have hu : ∃ s ∈ armRoute w g role, s.Contains (segmentAt P.segments i).finish :=
    ⟨_,P.segment_mem i (by have h : i+1 < P.segments.length := hi.1; omega),P.finish_contains w G i (by have h : i+1 < P.segments.length := hi.1; omega)⟩
  rcases (armSpec w g other).code_wall_trace w hw (armSpec_geometry w g other) d hd q hq with h | h
  · obtain ⟨u,hu',hb⟩ := h
    exact footprint_ne (w := w)
      (fun hh => armRoutes_separated_wide w g hne hu hu' (nearby_of_le (by omega) hh)) ha hb
  · obtain ⟨u,hu',hb⟩ := h
    apply Ne.symm
    exact footprint_ne (w := w)
      (fun hh => armRoute_tail_separated w g (Ne.symm hne) hu' hu
        (nearby_of_le (by unfold FiniteGeometry.origin FiniteTools.radius; omega) hh)) hb ha

private theorem arm_turn_action_ne_core (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (role : Fin 3)
    (i : ℕ) (hi : (armSpec w g role).hasTurn i)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (q : Cell ((PrimitiveCode.core g).instanceOf w hw).width ((PrimitiveCode.core g).instanceOf w hw).height) :
    ((armSpec w g role).turn i).actionWorld w hw p ≠ (PrimitiveCode.core g).world w hw q := by
  let P := armSpec w g role
  have G : P.Geometry w := armSpec_geometry w g role
  have ha := P.turn_action_at w hw G i hi p hp
  exact core_tail_ne w hw g role 4 (by unfold FiniteGeometry.origin; omega)
    ⟨_,P.segment_mem_tail (i+1) hi.1 (by omega),P.start_contains w G (i+1) hi.1⟩ ha q

private theorem gate_turn_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (t : TurnCode)
    (ht : PrimitiveCode.turn t ∈ gateCodes w g)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (d : PrimitiveCode) (hd : d ∈ gateCodes w g)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    t.actionWorld w hw p ≠ d.world w hw q := by
  obtain ⟨role,i,hi,rfl⟩ := gate_turn_origin w g t ht
  rw [gateCodes_eq_specs] at hd
  rcases List.mem_cons.mp hd with rfl | hd
  · exact arm_turn_action_ne_core w hw g role i hi p hp q
  · obtain ⟨other,_,hd⟩ := List.mem_flatMap.mp hd
    by_cases hro : role = other
    · subst other
      exact (armSpec w g role).turn_action_ne_codes_wall w hw (armSpec_geometry w g role) i hi p hp d hd q hq
    · exact different_arms_turn_action_ne_wall w hw g role other hro i hi p hp d hd q hq

theorem local_turn_action_ne_wall (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (t : TurnCode)
    (ht : PrimitiveCode.turn t ∈ FiniteSourceInventory.localCodes w code)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (d : PrimitiveCode) (hd : d ∈ FiniteSourceInventory.localCodes w code)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    t.actionWorld w hw p ≠ d.world w hw q := by
  cases code with
  | none => simp [FiniteSourceInventory.localCodes] at ht
  | some code =>
    cases code with
    | inl g => exact gate_turn_action_ne_wall w hw g.2 t ht p hp d hd q hq
    | inr a =>
      obtain ⟨i,hi,rfl⟩ := (wireSpec w a.2).turn_code_origin t ht
      exact (wireSpec w a.2).turn_action_ne_codes_wall w hw (wireSpec_geometry w a.2) i hi p hp d hd q hq

end PushPuzzle.PushS.FiniteRouting

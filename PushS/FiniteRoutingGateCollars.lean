/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCollarGeometry

/-! Actual gate collar marks belong to exactly the terminal straight arm at that face. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

def gatePortLine (w : ℕ) (g : GateTileState) (role : Fin 3) : LineCode :=
  (armSpec w g role).line ((armRoute w g role).length-1)

theorem gatePortLine_good (w : ℕ) (g : GateTileState) (role : Fin 3) : LineGood w (gatePortLine w g role).segment :=
  (armSpec w g role).line_good w (armSpec_geometry w g role) _
    (by change (armRoute w g role).length-1 < (armRoute w g role).length; rw [armRoute_length,route_length]; omega)

theorem gate_actor_collar (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    ∃ role : Fin 3, c = .line (gatePortLine w g role) ∧
      PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ((interior_not_collar w face (core_window_interior w hw g
      (if goal then (PrimitiveCode.matching w hw (.core g)).target l else
        (PrimitiveCode.matching w hw (.core g)).source l))) hf).elim
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    let P := armSpec w g role
    have G : P.Geometry w := armSpec_geometry w g role
    change c ∈ P.codes at hc
    obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
    have hi' := List.mem_range.mp hi
    rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
    · by_cases hn : i+1 < (armRoute w g role).length
      · exact ((interior_not_collar w face (arm_nonlast_actor_interior w hw g role i hn goal l)) hf).elim
      · have he : i = (armRoute w g role).length-1 := by change i < (armRoute w g role).length at hi'; omega
        subst i
        obtain ⟨u,hu,ha⟩ := P.line_actor_at w hw G _ hi' goal l
        exact ⟨role,rfl,arm_last_collar_face w g role face 1 (by unfold padding; omega) hu ha hf⟩
    · exact ((interior_not_collar w face (arm_turn_window_interior w hw g role i ht
        (if goal then (PrimitiveCode.matching w hw (.turn (P.turn i))).target l else
          (PrimitiveCode.matching w hw (.turn (P.turn i))).source l))) hf).elim

theorem gate_wall_collar (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) :
    ∃ role : Fin 3, c = .line (gatePortLine w g role) ∧
      PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face := by
  rw [gateCodes_eq_specs] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ((interior_not_collar w face (core_window_interior w hw g p)) hf).elim
  · obtain ⟨role,_,hc⟩ := List.mem_flatMap.mp hc
    let P := armSpec w g role
    have G : P.Geometry w := armSpec_geometry w g role
    change c ∈ P.codes at hc
    obtain ⟨i,hi,hc⟩ := List.mem_flatMap.mp hc
    have hi' := List.mem_range.mp hi
    rcases (P.mem_block i c).mp hc with rfl | ⟨ht,rfl⟩
    · by_cases hn : i+1 < (armRoute w g role).length
      · exact ((interior_not_collar w face (arm_nonlast_wall_interior w hw g role i hn p hp)) hf).elim
      · have he : i = (armRoute w g role).length-1 := by change i < (armRoute w g role).length at hi'; omega
        subst i
        obtain ⟨u,hu,ha⟩ := P.line_wall_at w hw G _ hi' p hp
        exact ⟨role,rfl,arm_last_collar_face w g role face (w+1) (by unfold padding; omega) hu ha hf⟩
    · exact ((interior_not_collar w face (arm_turn_window_interior w hw g role i ht p)) hf).elim

private theorem line_endpoint_actor_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (goal : Bool) (l : (PrimitiveCode.line c).Labels w) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) ((PrimitiveCode.line c).actor w hw goal l) := by
  rw [line_actor w hw c hc goal l,hd]
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  cases face <;> dsimp [SameLane,Travels,advance,Line.along,Direction.opposite,boundaryPoint] at * <;> omega

private theorem line_endpoint_wall_off_lane (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (hc : LineGood w c.segment)
    (face : Direction) (incoming : Bool) (hd : segmentDirection c.segment = face)
    (he : c.segment.finish = advance face.opposite (boundaryPoint w face) incoming.toNat)
    (p : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hp : p ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) ((PrimitiveCode.line c).world w hw p) := by
  obtain ⟨_,_,hn⟩ := line_wall_envelope w hw c hc p hp
  have ht := segment_travels c.segment hc.1
  rw [hd,he] at ht
  rw [hd] at hn
  cases face <;> dsimp [SameLane,Travels,advance,Line.along,Direction.opposite,boundaryPoint] at * <;> omega

theorem gate_actor_collar_lane (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g) (goal : Bool) (l : c.Labels w) (face : Direction)
    (hf : InCollar w face (c.actor w hw goal l)) :
    SameLane face (Line.along w face (boundaryPoint w face) 0) (c.actor w hw goal l) := by
  obtain ⟨role,rfl,hd⟩ := gate_actor_collar w hw g c hc goal l face hf
  apply line_endpoint_actor_lane w hw _ (gatePortLine_good w g role) face (g.incoming.get role)
  · exact (armSpec_last_direction w g role).trans hd
  · simpa only [gatePortLine,←hd] using armSpec_last_finish w g role

theorem gate_wall_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (g : GateTileState) (c : PrimitiveCode)
    (hc : c ∈ gateCodes w g)
    (p : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height)
    (hp : p ∈ (c.instanceOf w hw).board.walls) (face : Direction)
    (hf : InCollar w face (c.world w hw p)) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) (c.world w hw p) := by
  obtain ⟨role,rfl,hd⟩ := gate_wall_collar w hw g c hc p hp face hf
  apply line_endpoint_wall_off_lane w hw _ (gatePortLine_good w g role) face (g.incoming.get role) _ _ p hp
  · exact (armSpec_last_direction w g role).trans hd
  · simpa only [gatePortLine,←hd] using armSpec_last_finish w g role

end PushPuzzle.PushS.FiniteRouting

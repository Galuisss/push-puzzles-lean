/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnActionWalls

/-! The complete four-box turn action avoids every wall in its literal routed path. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace PathSpec

theorem turn_action_at (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hp : p ∈ FiniteTools.turnActive w) :
    Nearby 4 ((P.turn i).actionWorld w hw p)
      (padding w+(segmentAt P.segments (i+1)).start.1,padding w+(segmentAt P.segments (i+1)).start.2) := by
  have ha := (P.turn i).action_footprint w hw p hp
  change Nearby 4 ((P.turn i).actionWorld w hw p)
    (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) at ha
  simpa only [P.join_eq w G i hi.1] using ha

private theorem turn_action_ne_line_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (j : ℕ) (hj : j < P.segments.length)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (q : Cell ((PrimitiveCode.line (P.line j)).instanceOf w hw).width ((PrimitiveCode.line (P.line j)).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line (P.line j)).instanceOf w hw).board.walls) :
    (P.turn i).actionWorld w hw p ≠ (PrimitiveCode.line (P.line j)).world w hw q := by
  have H := P.junction_contract w G i hi
  by_cases hij : j = i
  · subst j
    exact incoming_wall_ne_turn_action w hw _ H.incoming_good _ H.incoming_direction H.incoming_finish
      (P.incoming_side i hi) p hp q hq
  by_cases hij' : j = i+1
  · subst j
    exact outgoing_wall_ne_turn_action w hw _ H.outgoing_good _ H.perpendicular H.outgoing_direction H.outgoing_start
      (P.outgoing_side i hi) p hp q hq
  have ha := (P.turn i).action_footprint w hw p hp
  obtain ⟨u,hu,hb⟩ := P.line_wall_at w hw G j hj q hq
  by_cases hji : j < i
  · change Nearby 4 ((P.turn i).actionWorld w hw p)
      (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) at ha
    rw [P.join_eq w G i hi.1] at ha
    exact Ne.symm (P.marks_ne w G j (i+1) hj hi.1 (by omega) (w+1) 4
      (by unfold FiniteGeometry.origin; omega) hu (P.start_contains w G (i+1) hi.1) hb ha)
  · exact P.marks_ne w G i j (by have hh := hi.1; omega) hj (by omega) 4 (w+1)
      (by unfold FiniteGeometry.origin; omega) (P.finish_contains w G i (by have hh := hi.1; omega)) hu ha hb

private theorem turn_action_ne_turn_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : P.hasTurn i) (hj : P.hasTurn j)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hq : q ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (P.turn i).actionWorld w hw p ≠ (PrimitiveCode.turn (P.turn j)).world w hw q := by
  by_cases he : i = j
  · subst j
    exact (P.turn i).action_ne_own_wall w hw p hp q hq
  have ha := (P.turn i).action_footprint w hw p hp
  have hb := P.turn_wall_at w hw j q
  by_cases hij : i < j
  · rw [P.join_eq w G j hj.1] at hb
    exact P.marks_ne w G i (j+1) (by have hh := hi.1; omega) hj.1 (by omega) 4 (FiniteTools.radius w)
      (by unfold FiniteGeometry.origin FiniteTools.radius; omega)
      (P.finish_contains w G i (by have hh := hi.1; omega)) (P.start_contains w G (j+1) hj.1) ha hb
  · change Nearby 4 ((P.turn i).actionWorld w hw p)
      (padding w+(segmentAt P.segments i).finish.1,padding w+(segmentAt P.segments i).finish.2) at ha
    rw [P.join_eq w G i hi.1] at ha
    exact Ne.symm (P.marks_ne w G j (i+1) (by have hh := hj.1; omega) hi.1 (by omega)
      (FiniteTools.radius w) 4 (by unfold FiniteGeometry.origin FiniteTools.radius; omega)
      (P.finish_contains w G j (by have hh := hj.1; omega)) (P.start_contains w G (i+1) hi.1) hb ha)

theorem turn_action_ne_codes_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : P.hasTurn i) (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (d : PrimitiveCode) (hd : d ∈ P.codes)
    (q : Cell (d.instanceOf w hw).width (d.instanceOf w hw).height) (hq : q ∈ (d.instanceOf w hw).board.walls) :
    (P.turn i).actionWorld w hw p ≠ d.world w hw q := by
  obtain ⟨j,hj,hd⟩ := List.mem_flatMap.mp hd
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block j d).mp hd with rfl | ⟨ht,rfl⟩
  · exact P.turn_action_ne_line_wall w hw G i hi j hj' p hp q hq
  · exact P.turn_action_ne_turn_wall w hw G i j hi ht p hp q hq

end PathSpec
end PushPuzzle.PushS.FiniteRouting

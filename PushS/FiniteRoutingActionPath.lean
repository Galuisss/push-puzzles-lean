/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionJunctions
public import PushS.FiniteRoutingActionCollinear
public import PushS.FiniteRoutingActionCrossing
public import PushS.FiniteRoutingActionClearance

/-! Every actual line action cell avoids every wall in its complete multi-segment path. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

private theorem LineCode.action_ne_own_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (q : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ (PrimitiveCode.line c).world w hw q := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  change q ∈ (Line.walls w atoms c.above).map (Line.rotation w atoms (segmentDirection c.segment)).cells.toEmbedding at hq
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hq
  intro h
  rw [←he] at h
  have hh := (PrimitiveCode.line c).world_injective w hw h
  have hpa := (Line.rotation w atoms (segmentDirection c.segment)).cells.injective hh
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  exact hb.2.2.2.2 (hpa ▸ ha)

namespace PathSpec

private theorem next_side (P : PathSpec) (i : ℕ) (hi : i+1 < P.segments.length) :
    (P.line i).desiredSide = (P.line (i+1)).above := by
  simp only [line,lineCodeAt,finalSide,entrySide,show i+1 ≠ P.segments.length by omega,
    show i+1 ≠ 0 by omega,ite_false,Nat.add_sub_cancel]

theorem incoming_side (P : PathSpec) (i : ℕ) (hi : P.hasTurn i) :
    (P.line i).desiredSide = turnSide (P.turn i).incoming (P.turn i).outgoing := by
  simp only [line,lineCodeAt,finalSide,turn,turnCodeAt,show i+1 ≠ P.segments.length by have := hi.1; omega,ite_false]

theorem outgoing_side (P : PathSpec) (i : ℕ) (hi : P.hasTurn i) :
    (P.line (i+1)).above = turnSide (P.turn i).incoming (P.turn i).outgoing := by
  rw [←P.next_side i hi.1]
  exact P.incoming_side i hi

private theorem action_ne_line_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : j < P.segments.length)
    : (P.line i).ActionClear w hw (P.line j) := by
  intro p hp q hq
  rcases lt_trichotomy i j with hij | hij | hij
  · by_cases hnext : j = i+1
    · subst j
      by_cases ht : P.hasTurn i
      · exact incoming_action_ne_outgoing_wall w hw _ _ _ (P.junction_contract w G i ht)
          (P.outgoing_side i ht) p hp q hq
      · have H := P.collinear_contract w G i hj ht
        exact collinear_action_ne_next_wall w hw _ _ H.first_good H.next_good H.directions H.joined
          (P.next_side i hj) p hp q hq
    · exact P.action_ne_line_far w hw G i j hi hj (Or.inl (by omega)) p hp q hq
  · subst j
    exact (P.line i).action_ne_own_wall w hw p hp q hq
  · by_cases hnext : i = j+1
    · subst i
      by_cases ht : P.hasTurn j
      · exact outgoing_action_ne_incoming_wall w hw _ _ _ (P.junction_contract w G j ht)
          (P.incoming_side j ht) p hp q hq
      · have H := P.collinear_contract w G j hi ht
        exact collinear_action_ne_previous_wall w hw _ _ H.first_good H.next_good H.directions H.joined
          (P.next_side j hi) p hp q hq
    · exact P.action_ne_line_far w hw G i j hi hj (Or.inr (by omega)) p hp q hq

private theorem action_ne_turn_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i j : ℕ) (hi : i < P.segments.length) (hj : P.hasTurn j)
    (p : Cell (Line.width w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide)) (P.line i).above (P.line i).last)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hq : q ∈ ((PrimitiveCode.turn (P.turn j)).instanceOf w hw).board.walls) :
    (P.line i).actionWorld w hw p ≠ (PrimitiveCode.turn (P.turn j)).world w hw q := by
  have H := P.junction_contract w G j hj
  by_cases hij : i = j
  · subst i
    exact incoming_action_ne_turn_wall w hw _ _ H.incoming_good H.perpendicular H.incoming_last
      H.incoming_direction H.incoming_finish (P.incoming_side j hj) p hp q hq
  by_cases hij' : i = j+1
  · subst i
    exact outgoing_action_ne_turn_wall w hw _ _ H.outgoing_good H.perpendicular
      H.outgoing_direction H.outgoing_start (P.outgoing_side j hj) p hp q hq
  exact P.action_ne_turn_far w hw G i j hi hj hij hij' p hp q

theorem action_ne_codes_wall (P : PathSpec) (w : ℕ) (hw : 2 ≤ w) (G : P.Geometry w)
    (i : ℕ) (hi : i < P.segments.length)
    (p : Cell (Line.width w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength (P.line i).segment)
      ((P.line i).above != (P.line i).desiredSide)) (P.line i).above (P.line i).last)
    (c : PrimitiveCode) (hc : c ∈ P.codes)
    (q : Cell (c.instanceOf w hw).width (c.instanceOf w hw).height) (hq : q ∈ (c.instanceOf w hw).board.walls) :
    (P.line i).actionWorld w hw p ≠ c.world w hw q := by
  obtain ⟨j,hj,hc⟩ := List.mem_flatMap.mp hc
  have hj' := List.mem_range.mp hj
  rcases (P.mem_block j c).mp hc with rfl | ⟨ht,rfl⟩
  · exact P.action_ne_line_wall w hw G i j hi hj' p hp q hq
  · exact P.action_ne_turn_wall w hw G i j hi ht p hp q hq

end PathSpec
end PushPuzzle.PushS.FiniteRouting

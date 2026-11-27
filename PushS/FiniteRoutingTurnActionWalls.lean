/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingTurnActionCoordinates
public import PushS.FiniteRoutingActionEndBand
public import PushS.FiniteRoutingActionSeams

/-! Every real turn action avoids its own guards and both adjoining straight programs. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

theorem TurnCode.action_footprint (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w) :
    Nearby 4 (t.actionWorld w hw p) (padding w+t.corner.1,padding w+t.corner.2) := by
  have hb := (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mp hp
  have hr := Turn.orientation_coordinates w t.incoming t.outgoing p
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [coordinates] at hx hy
  change Nearby 4 (Turn.offsetX w t.corner+((Turn.orientation w t.incoming t.outgoing).cells p).1.val,
    Turn.offsetY w t.corner+((Turn.orientation w t.incoming t.outgoing).cells p).2.val) _
  rw [hx,hy]
  clear hr hx hy
  by_cases hs : t.outgoing = rightTurn t.incoming
  all_goals cases hd : t.incoming
  all_goals simp only [hd] at hs
  all_goals simp only [Nearby,Turn.quarterCoordinates,Turn.offsetX,Turn.offsetY,hs,↓reduceIte]
  all_goals dsimp only at hb
  all_goals unfold FiniteTools.side FiniteTools.radius padding at *; omega

theorem TurnCode.action_ne_own_wall (w : ℕ) (hw : 2 ≤ w) (t : TurnCode)
    (p : Cell (FiniteTools.side w) (FiniteTools.side w)) (hp : p ∈ FiniteTools.turnActive w)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hq : q ∈ ((PrimitiveCode.turn t).instanceOf w hw).board.walls) :
    t.actionWorld w hw p ≠ (PrimitiveCode.turn t).world w hw q := by
  change q ∈ (FiniteTools.turnWalls w).map (Turn.orientation w t.incoming t.outgoing).cells.toEmbedding at hq
  obtain ⟨a,ha,he⟩ := Finset.mem_map.mp hq
  intro hh
  rw [←he] at hh
  have heq := (Turn.orientation w t.incoming t.outgoing).cells.injective ((PrimitiveCode.turn t).world_injective w hw hh)
  exact FiniteTools.turnActive_floor w hp (heq ▸ ha)

theorem incoming_wall_ne_turn_action (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hside : c.desiredSide = turnSide t.incoming t.outgoing)
    : t.LineClear w hw c := by
  intro p hp q hq
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  obtain ⟨a,ha,he⟩ := c.wall_world w hw q hq
  intro hh
  rw [he] at hh
  have hxy := c.incoming_turn_coordinates w hw hc t hd hf a p hh.symm
  have hb := (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mp hp
  have hs : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hx : FiniteTools.radius w+Line.span w atoms ≤ a.1.val+(w+1) := by dsimp only at hb; omega
  have hband := Line.program_end_wall_band w _ (c.above != c.desiredSide) c.above a ha hx
  have hside' : Line.exitSide c.above atoms = turnSide t.incoming t.outgoing := (c.exitSide_eq w).trans hside
  rw [hside'] at hband
  by_cases ht : t.outgoing = rightTurn t.incoming
  all_goals simp only [ht,↓reduceIte] at hxy
  all_goals simp only [Line.stockBand_turnSide,ht,↓reduceIte] at hband
  all_goals dsimp only at hb
  all_goals unfold FiniteTools.side FiniteTools.radius at *; omega

theorem outgoing_wall_ne_turn_action (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (hturn : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing) (hf : c.segment.start = advance t.outgoing t.corner 1)
    (hside : c.above = turnSide t.incoming t.outgoing)
    : t.LineClear w hw c := by
  intro p hp q hq
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  obtain ⟨a,ha,he⟩ := c.wall_world w hw q hq
  intro hh
  rw [he] at hh
  have hxy := c.outgoing_turn_coordinates w hw hc t hturn hd hf a p hh.symm
  have hb := (FiniteGeometry.Rectangle.mem_cells _ _ _ _).mp hp
  have hx : a.1.val < FiniteTools.radius w+2*Line.buffer w := by dsimp only at hb; unfold Line.buffer; omega
  have hband := Line.program_first_wall_band w _ (c.above != c.desiredSide) c.above a ha hx
  conv at hband => arg 2; rw [hside]
  by_cases ht : t.outgoing = rightTurn t.incoming
  all_goals simp only [ht,↓reduceIte] at hxy
  all_goals simp only [Line.stockBand_turnSide,ht,↓reduceIte] at hband
  all_goals dsimp only at hb
  all_goals unfold FiniteTools.side FiniteTools.radius at *; omega

end PushPuzzle.PushS.FiniteRouting

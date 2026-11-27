/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionLocal
public import PushS.FiniteRoutingWorldCoordinates
public import PushS.FiniteTurn

/-! Exact canonical coordinates at both sides of the literal four-box routing turn. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

namespace LineCode

-- Compare the literal rotations and translations in each of the four incoming directions.
set_option maxHeartbeats 1000000 in
theorem incoming_turn_coordinates (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (a : c.ActionCell w) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (he : c.actionWorld w hw a = t.actionWorld w hw p) :
    a.1.val = segmentLength c.segment+2+p.1.val ∧
      a.2.val = if t.outgoing = rightTurn t.incoming then p.2.val else FiniteTools.side w-(p.2.val+1) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hs : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hs' : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = segmentLength c.segment := hs
  rw [LineCode.actionWorld_eq,TurnCode.actionWorld_eq] at he
  rw [hd] at he
  have heX := congrArg Prod.fst he
  have heY := congrArg Prod.snd he
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  have hal := a.1.isLt
  have hay := a.2.isLt
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hlen := hc.2.1
  by_cases ht : t.outgoing = rightTurn t.incoming
  all_goals simp only [ht,↓reduceIte] at heX heY ⊢
  all_goals cases di : t.incoming
  all_goals simp only [di] at htravel heX heY
  all_goals dsimp [coordinates,Line.rotatedCoordinates,Turn.quarterCoordinates,Line.offsetX,Line.offsetY,
    Turn.offsetX,Turn.offsetY,Line.anchor,Travels,advance,Direction.opposite] at htravel heX heY
  all_goals simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hs,hs',padding] at *
  all_goals constructor <;> omega

-- The eight perpendicular orientations share the same scalar outgoing coordinate formula.
set_option maxHeartbeats 1000000 in
theorem outgoing_turn_coordinates (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (t : TurnCode) (hturn : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing) (hf : c.segment.start = advance t.outgoing t.corner 1)
    (a : c.ActionCell w) (p : Cell (FiniteTools.side w) (FiniteTools.side w))
    (he : c.actionWorld w hw a = t.actionWorld w hw p) :
    a.1.val+1 = p.2.val ∧
      a.2.val = if t.outgoing = rightTurn t.incoming then FiniteTools.side w-(p.1.val+1) else p.1.val := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hs : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hs' : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = segmentLength c.segment := hs
  rw [LineCode.actionWorld_eq,TurnCode.actionWorld_eq] at he
  rw [hd,hf] at he
  have heX := congrArg Prod.fst he
  have heY := congrArg Prod.snd he
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  have hal := a.1.isLt
  have hay := a.2.isLt
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hlen := hc.2.1
  clear he
  cases di : t.incoming <;> cases do' : t.outgoing <;>
    simp [di,do',Perpendicular,rightTurn,Direction.opposite] at hturn ⊢ <;>
    simp only [di,do',rightTurn,↓reduceIte] at htravel heX heY <;>
    dsimp [coordinates,Line.rotatedCoordinates,Turn.quarterCoordinates,Line.offsetX,Line.offsetY,
      Turn.offsetX,Turn.offsetY,Line.anchor,Travels,advance,Direction.opposite] at htravel heX heY <;>
    simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hs,hs',padding] at * <;>
    constructor <;> omega

end LineCode
end PushPuzzle.PushS.FiniteRouting

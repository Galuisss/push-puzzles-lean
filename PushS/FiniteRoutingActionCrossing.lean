/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionGuards
public import PushS.FiniteRoutingActionEndBand
public import PushS.FiniteRoutingActionFootprint
public import PushS.FiniteRoutingPathJunctions
public import PushS.FiniteRoutingWorldCoordinates

/-! Adjacent perpendicular strips meet only their protected stock collars. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls Line.program Line.span FiniteTools.side

-- Compare the eight perpendicular placements before applying the literal first stock guard.
set_option maxHeartbeats 1000000 in
theorem incoming_action_ne_outgoing_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (hside : e.above = turnSide t.incoming t.outgoing)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (q : Cell ((PrimitiveCode.line e).instanceOf w hw).width ((PrimitiveCode.line e).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line e).instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ (PrimitiveCode.line e).world w hw q := by
  obtain ⟨a,ha,he⟩ := e.wall_world w hw q hq
  obtain ⟨_,hb⟩ := (Line.Action.mem_active w _ c.above c.last p).mp hp
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) H.incoming_good.2.1
  intro hh
  rw [he] at hh
  have hxy := JunctionContract.action_coordinates w hw c t e H p a hh
  have hnear : a.1.val < FiniteTools.radius w+2*Line.buffer w := by
    split at hxy <;> unfold Line.buffer FiniteTools.radius at * <;> omega
  have hband := Line.program_first_wall_band w _ (e.above != e.desiredSide) e.above a ha hnear
  have hside' : Line.StockBand w (turnSide t.incoming t.outgoing) a.2.val :=
    (congrArg (fun side => Line.StockBand w side a.2.val) hside).mp hband
  by_cases ht : t.outgoing = rightTurn t.incoming
  all_goals simp only [ht,↓reduceIte] at hxy
  all_goals simp only [Line.stockBand_turnSide,ht,↓reduceIte] at hside'
  all_goals unfold FiniteTools.radius at *; omega

-- The reverse contact uses the final stock collar, with the same eight physical placements.
set_option maxHeartbeats 1000000 in
theorem outgoing_action_ne_incoming_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (e : LineCode)
    (H : JunctionContract w c t e) (hside : c.desiredSide = turnSide t.incoming t.outgoing)
    (p : Cell (Line.width w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength e.segment) (e.above != e.desiredSide)) e.above e.last)
    (q : Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height)
    (hq : q ∈ ((PrimitiveCode.line c).instanceOf w hw).board.walls) :
    e.actionWorld w hw p ≠ (PrimitiveCode.line c).world w hw q := by
  obtain ⟨a,ha,he⟩ := c.wall_world w hw q hq
  obtain ⟨hu,hb⟩ := (Line.Action.mem_active w _ e.above e.last p).mp hp
  have hspan := Line.program_span_of_bound w _ (c.above != c.desiredSide) H.incoming_good.2.1
  intro hh
  rw [he] at hh
  have hxy := JunctionContract.action_coordinates w hw c t e H a p hh.symm
  have hnear : FiniteTools.radius w+Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) ≤ a.1.val+(w+1) := by
    split at hxy <;> unfold FiniteTools.radius at * <;> omega
  have hband := Line.program_end_wall_band w _ (c.above != c.desiredSide) c.above a ha hnear
  have hside' : Line.exitSide c.above (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) = turnSide t.incoming t.outgoing := by
    rw [←hside]
    cases c.above <;> cases c.desiredSide <;> simp [Line.program_exitSide]
  rw [hside'] at hband
  have hmin : FiniteTools.radius w ≤ p.1.val := by rcases hu with hu | hu | hu <;> omega
  by_cases ht : t.outgoing = rightTurn t.incoming
  all_goals simp only [ht,↓reduceIte] at hxy
  all_goals simp only [Line.stockBand_turnSide,ht,↓reduceIte] at hband
  all_goals unfold FiniteTools.radius at *; omega

end PushPuzzle.PushS.FiniteRouting

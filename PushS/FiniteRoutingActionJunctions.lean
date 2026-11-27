/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionFootprint
public import PushS.FiniteRoutingJunctions

/-! The literal end stock guards exclude foreign concave-turn walls from actual line action cells. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls
attribute [local irreducible] Line.rectangles Line.program Line.exitSide Line.span

-- Compare both literal turn rectangles in each of the eight perpendicular orientations.
set_option maxHeartbeats 1000000 in
theorem incoming_action_ne_turn_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hlast : c.last = false) (hd : segmentDirection c.segment = t.incoming)
    (hf : c.segment.finish = advance t.incoming.opposite t.corner 2)
    (hside : c.desiredSide = turnSide t.incoming t.outgoing)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hq : q ∈ ((PrimitiveCode.turn t).instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ (PrimitiveCode.turn t).world w hw q := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  change Line.Action.UsedPoint w atoms c.above c.last p at hu
  change FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w atoms+2 ∧
    FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ p ∉ Line.walls w atoms c.above at hb
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hlenLiteral : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) =
      segmentLength c.segment := hlen
  have hs : Line.exitSide c.above atoms = turnSide t.incoming t.outgoing := by
    rw [←hside]
    cases ha : c.above <;> cases hz : c.desiredSide <;> simp [atoms,ha,hz,Line.program_exitSide]
  have htravel := segment_travels c.segment hc.1
  rw [hd,hf] at htravel
  obtain ⟨a,ha,he⟩ := turn_wall_coordinates w hw t q hq
  unfold FiniteTools.turnWalls at ha
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
  have hr := ((FiniteTools.turnRectangle w i).mem_cells _ _ a).mp hi
  intro h
  have hx := congrArg Prod.fst (h.trans he)
  have hy := congrArg Prod.snd (h.trans he)
  have hrot := Line.rotation_coordinates w atoms (segmentDirection c.segment) p
  have hrotX := congrArg Prod.fst hrot
  have hrotY := congrArg Prod.snd hrot
  dsimp only [coordinates] at hrotX hrotY
  change Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).1.val = _ at hx
  change Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).2.val = _ at hy
  rw [hrotX,hd] at hx
  rw [hrotY,hd] at hy
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hax := a.1.isLt
  have hay := a.2.isLt
  have hbX0 := hb.1
  have hbX1 := hb.2.1
  have hbY0 := hb.2.2.1
  have hbY1 := hb.2.2.2.1
  have hl := hc.2.1
  apply hb.2.2.2.2
  apply Line.program_last_stock_wall w (segmentLength c.segment) (c.above != c.desiredSide) c.above p
  all_goals clear hp hb ha hi h hq he hrot hrotX hrotY
  all_goals try rw [hs]
  all_goals cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases i <;>
    simp only [hdi,hdo] at ht hx hy htravel ⊢ <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at ht
  all_goals dsimp [Line.Action.UsedPoint,Line.StockBand,turnSide,rightTurn,Turn.quarterCoordinates,
    Line.rotatedCoordinates,FiniteTools.turnRectangle,Turn.offsetX,Turn.offsetY,Line.offsetX,Line.offsetY,
    Line.anchor,Travels,advance,Direction.opposite,coordinates] at hu hr hx hy htravel ⊢
  all_goals simp [hlast] at hu hx hy ⊢
  all_goals simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,Line.buffer,hlen,hlenLiteral,padding]
    at hu hr hx hy htravel hpx hpy hax hay hbX0 hbX1 hbY0 hbY1 ⊢
  all_goals omega

-- Compare both literal turn rectangles against the actual first stock guard in all orientations.
set_option maxHeartbeats 1000000 in
theorem outgoing_action_ne_turn_wall (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (hc : LineGood w c.segment) (ht : Perpendicular t.incoming t.outgoing)
    (hd : segmentDirection c.segment = t.outgoing)
    (hs : c.segment.start = advance t.outgoing t.corner 1)
    (hside : c.above = turnSide t.incoming t.outgoing)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last)
    (q : Cell (FiniteTools.side w) (FiniteTools.side w))
    (hq : q ∈ ((PrimitiveCode.turn t).instanceOf w hw).board.walls) :
    c.actionWorld w hw p ≠ (PrimitiveCode.turn t).world w hw q := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  change Line.Action.UsedPoint w atoms c.above c.last p at hu
  change FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w atoms+2 ∧
    FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ p ∉ Line.walls w atoms c.above at hb
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have hlenLiteral : Line.span w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) =
      segmentLength c.segment := hlen
  have htravel := segment_travels c.segment hc.1
  rw [hd,hs] at htravel
  obtain ⟨a,ha,he⟩ := turn_wall_coordinates w hw t q hq
  unfold FiniteTools.turnWalls at ha
  obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp ha
  have hr := ((FiniteTools.turnRectangle w i).mem_cells _ _ a).mp hi
  intro h
  have hx := congrArg Prod.fst (h.trans he)
  have hy := congrArg Prod.snd (h.trans he)
  have hrot := Line.rotation_coordinates w atoms (segmentDirection c.segment) p
  have hrotX := congrArg Prod.fst hrot
  have hrotY := congrArg Prod.snd hrot
  dsimp only [coordinates] at hrotX hrotY
  change Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).1.val = _ at hx
  change Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).2.val = _ at hy
  rw [hrotX,hd] at hx
  rw [hrotY,hd] at hy
  rw [hs] at hx hy
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  have hax := a.1.isLt
  have hay := a.2.isLt
  have hbX0 := hb.1
  have hbX1 := hb.2.1
  have hbY0 := hb.2.2.1
  have hbY1 := hb.2.2.2.1
  have hl := hc.2.1
  apply hb.2.2.2.2
  apply Line.program_first_stock_wall w (segmentLength c.segment) (c.above != c.desiredSide) c.above p
  all_goals clear hp hb ha hi h hq he hrot hrotX hrotY
  all_goals try
    apply (congrArg (fun side => Line.StockBand w side p.2.val) hside).mpr
  all_goals cases hdi : t.incoming <;> cases hdo : t.outgoing <;> fin_cases i <;>
    simp only [hdi,hdo] at ht hx hy htravel ⊢ <;>
    simp [Perpendicular,rightTurn,Direction.opposite] at ht
  all_goals dsimp [Line.Action.UsedPoint,Line.StockBand,turnSide,rightTurn,Turn.quarterCoordinates,
    Line.rotatedCoordinates,FiniteTools.turnRectangle,Turn.offsetX,Turn.offsetY,Line.offsetX,Line.offsetY,
    Line.anchor,Travels,advance,Direction.opposite,coordinates] at hu hr hx hy htravel ⊢
  all_goals simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,Line.buffer,hlen,hlenLiteral,padding]
    at hu hr hx hy htravel hpx hpy hax hay hbX0 hbX1 hbY0 hbY1 ⊢
  all_goals omega

end PushPuzzle.PushS.FiniteRouting

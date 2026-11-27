/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSharedSlots
public import PushS.FiniteRoutingLineNeighbors

/-! Literal neighboring line stock supplies the complete turn macro's fixed P and Q boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

def secondSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells
    (Line.cell w hw atoms phase (Line.secondLabel w (segmentLength c.segment) (c.above != c.desiredSide)))

def penultimateSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells
    (Line.cell w hw atoms phase (Line.penultimateLabel w (segmentLength c.segment) (c.above != c.desiredSide)))

def secondWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.secondSlot w hw phase)

def penultimateWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.penultimateSlot w hw phase)

theorem secondWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (phase : Bool) :
    c.secondWorld w hw phase = Line.along w (segmentDirection c.segment) c.segment.start (2+phase.toNat) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hc.2.1]
    exact segment_travels _ hc.1
  have h := Line.placement_cell w hw atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2 phase (Line.secondLabel w (segmentLength c.segment) (c.above != c.desiredSide))
  rw [Line.second_position] at h
  exact h

theorem penultimateWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (phase : Bool) :
    c.penultimateWorld w hw phase = Line.along w (segmentDirection c.segment).opposite c.segment.finish (2-phase.toNat) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [hlen]
    exact segment_travels _ hc.1
  have h := Line.placement_cell w hw atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2 phase (Line.penultimateLabel w (segmentLength c.segment) (c.above != c.desiredSide))
  rw [Line.penultimate_position] at h
  change c.penultimateWorld w hw phase =
    Line.along w (segmentDirection c.segment) c.segment.start (Line.span w atoms-2+phase.toNat) at h
  rw [h,hlen]
  rw [hlen] at ht
  have hp := Bool.toNat_le phase
  have hl := hc.2.1
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

end LineCode

namespace TurnCode

def fixtureSlot (w : ℕ) (c : TurnCode) (successor : Bool) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (Turn.orientation w c.incoming c.outgoing).cells
    (FiniteTools.turnMixedCell w false false (if successor then .successor else .predecessor))

def fixtureWorld (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (successor : Bool) : ℕ × ℕ :=
  (PrimitiveCode.turn c).world w hw (c.fixtureSlot w successor)

set_option maxRecDepth 65536 in
private theorem fixtureWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : TurnCode)
    (hc : Perpendicular c.incoming c.outgoing)
    (successor : Bool) : c.fixtureWorld w hw successor =
      Line.along w (if successor then c.outgoing else c.incoming.opposite) c.corner 4 := by
  let p := FiniteTools.turnMixedCell w false false (if successor then .successor else .predecessor)
  have hr := Turn.orientation_coordinates w c.incoming c.outgoing p
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only [coordinates] at hx hy
  change (Turn.offsetX w c.corner+((Turn.orientation w c.incoming c.outgoing).cells p).1.val,
    Turn.offsetY w c.corner+((Turn.orientation w c.incoming c.outgoing).cells p).2.val) = _
  rw [hx,hy]
  cases successor <;> cases hd : c.incoming <;> cases he : c.outgoing <;>
    simp [hd,he,Perpendicular,rightTurn,Direction.opposite] at hc <;>
    dsimp [p,Turn.quarterCoordinates,coordinates,FiniteTools.turnMixedCell,FiniteTools.turnMixedPoint,
      rightTurn,Turn.offsetX,Turn.offsetY,Line.along,Direction.opposite] <;>
    apply Prod.ext <;> simp only [FiniteTools.side,FiniteTools.radius,padding] <;> omega

end TurnCode

theorem JunctionContract.incoming_penultimate_predecessor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) : c.penultimateWorld w hw false = t.fixtureWorld w hw false := by
  rw [LineCode.penultimateWorld_eq w hw c H.incoming_good false,TurnCode.fixtureWorld_eq w hw t H.perpendicular false]
  simp only [Bool.false_eq_true,↓reduceIte,Bool.toNat_false,Nat.sub_zero,H.incoming_direction,H.incoming_finish]
  have ht := segment_travels c.segment H.incoming_good.1
  rw [H.incoming_direction,H.incoming_finish] at ht
  have hl := H.incoming_good.2.1
  cases hd : t.incoming <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem JunctionContract.outgoing_second_successor (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) : d.secondWorld w hw true = t.fixtureWorld w hw true := by
  rw [LineCode.secondWorld_eq w hw d H.outgoing_good true,TurnCode.fixtureWorld_eq w hw t H.perpendicular true]
  simp only [↓reduceIte,Bool.toNat_true,H.outgoing_direction,H.outgoing_start]
  have ht := segment_travels d.segment H.outgoing_good.1
  rw [H.outgoing_direction,H.outgoing_start] at ht
  have hl := H.outgoing_good.2.1
  exact outgoing_along_ray w _ t.outgoing d.segment.finish t.corner ht (by omega) 3 (by omega)

end PushPuzzle.PushS.FiniteRouting

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingPathLayout
public import PushS.FiniteRoutingBoundary

/-! Exact physical shared slots, including interfaces left to another primitive's owner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteTools.turnWalls

namespace LineCode

def firstSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells (Line.cell w hw atoms phase (Line.firstLabel w atoms))

def lastSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells (Line.cell w hw atoms phase (Line.lastLabel w atoms))

def firstWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.firstSlot w hw phase)

def lastWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (phase : Bool) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.lastSlot w hw phase)

theorem firstWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (phase : Bool) :
    c.firstWorld w hw phase = Line.along w (segmentDirection c.segment) c.segment.start phase.toNat := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hc.2.1]
    exact segment_travels _ hc.1
  have h := Line.placement_cell w hw atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2 phase (Line.firstLabel w atoms)
  rw [Line.program_position_first] at h
  exact h

theorem lastWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (phase : Bool) :
    c.lastWorld w hw phase = Line.along w (segmentDirection c.segment) c.segment.finish phase.toNat := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have ht : Travels (segmentDirection c.segment) c.segment.start c.segment.finish (Line.span w atoms) := by
    rw [Line.program_span_of_bound w _ _ hc.2.1]
    exact segment_travels _ hc.1
  exact Line.placed_last_slot w hw atoms (segmentDirection c.segment) c.segment.start c.segment.finish
    ht hc.2.2.1 hc.2.2.2 phase

end LineCode

namespace TurnCode

def slot (w : ℕ) (c : TurnCode) (phase : Bool) (i : Fin 2) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (Turn.orientation w c.incoming c.outgoing).cells (Turn.cell w phase i)

def worldSlot (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (phase : Bool) (i : Fin 2) : ℕ × ℕ :=
  (PrimitiveCode.turn c).world w hw (c.slot w phase i)

private theorem worldSlot_actor (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) (phase : Bool) (i : Fin 2) :
    c.worldSlot w hw phase i =
      (PrimitiveCode.turn {c with initial := phase,target := phase}).actor w hw false i := rfl

end TurnCode

private theorem JunctionContract.incoming_shared (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (d : LineCode)
    (H : JunctionContract w c t d) (goal : Bool) :
    c.lastWorld w hw (if goal then t.target else t.initial) =
      (PrimitiveCode.turn t).actor w hw goal (0 : Fin 2) := by
  rw [LineCode.lastWorld_eq w hw c H.incoming_good,turn_actor w hw t H.perpendicular goal 0]
  simp only [ite_true,H.incoming_direction,H.incoming_finish]
  have ht := segment_travels c.segment H.incoming_good.1
  rw [H.incoming_direction,H.incoming_finish] at ht
  have hl := H.incoming_good.2.1
  have hp := Bool.toNat_le (if goal then t.target else t.initial)
  cases hdi : t.incoming <;> simp only [hdi] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

private theorem JunctionContract.outgoing_shared (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode)
    (d : LineCode)
    (H : JunctionContract w c t d) (goal : Bool) :
    d.firstWorld w hw (if goal then t.target else t.initial) =
      (PrimitiveCode.turn t).actor w hw goal (1 : Fin 2) := by
  rw [LineCode.firstWorld_eq w hw d H.outgoing_good,turn_actor w hw t H.perpendicular goal 1]
  simp only [show (1 : Fin 2) ≠ 0 by decide,↓reduceIte,H.outgoing_direction,H.outgoing_start]
  have ht := segment_travels d.segment H.outgoing_good.1
  rw [H.outgoing_direction,H.outgoing_start] at ht
  have hl := H.outgoing_good.2.1
  have hp := Bool.toNat_le (if goal then t.target else t.initial)
  cases hdo : t.outgoing <;> simp only [hdo] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem CollinearContract.shared (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (H : CollinearContract w c d) (phase : Bool) : c.lastWorld w hw phase = d.firstWorld w hw phase := by
  rw [LineCode.lastWorld_eq w hw c H.first_good,LineCode.firstWorld_eq w hw d H.next_good,H.directions,H.joined]

theorem JunctionContract.incoming_shared_phase (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (phase : Bool) : c.lastWorld w hw phase = t.worldSlot w hw phase 0 := by
  rw [TurnCode.worldSlot_actor]
  have H' : JunctionContract w c {t with initial := phase,target := phase} d :=
    ⟨H.incoming_good,H.outgoing_good,H.perpendicular,H.incoming_last,H.outgoing_first,
      H.incoming_direction,H.incoming_finish,H.outgoing_direction,H.outgoing_start⟩
  exact JunctionContract.incoming_shared w hw c _ d H' false

theorem JunctionContract.outgoing_shared_phase (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) (phase : Bool) : d.firstWorld w hw phase = t.worldSlot w hw phase 1 := by
  rw [TurnCode.worldSlot_actor]
  have H' : JunctionContract w c {t with initial := phase,target := phase} d :=
    ⟨H.incoming_good,H.outgoing_good,H.perpendicular,H.incoming_last,H.outgoing_first,
      H.incoming_direction,H.incoming_finish,H.outgoing_direction,H.outgoing_start⟩
  exact JunctionContract.outgoing_shared w hw c _ d H' false

end PushPuzzle.PushS.FiniteRouting

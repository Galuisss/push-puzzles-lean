/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingSharedSlots
public import PushS.FiniteRoutingLineReadout
public import PushS.FiniteRoutingSeamOwners

/-! Literal physical readout support caps at the adjacent turn's real floor corner. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

def capIndex (w : ℕ) (atoms : List Line.Atom) (before : Bool) : Fin (Line.span w atoms+4) :=
  if before then 0 else ⟨Line.span w atoms+3,by omega⟩

def capSlot (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (before : Bool) :
    Cell ((PrimitiveCode.line c).instanceOf w hw).width ((PrimitiveCode.line c).instanceOf w hw).height :=
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  (Line.rotation w atoms (segmentDirection c.segment)).cells (Line.Readout.rail w atoms (capIndex w atoms before))

def capWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (before : Bool) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw (c.capSlot w hw before)

theorem capWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment) (before : Bool) :
    c.capWorld w hw before = if before then Line.along w (segmentDirection c.segment).opposite c.segment.start 1
      else Line.along w (segmentDirection c.segment) c.segment.finish 2 := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  have ht := segment_travels c.segment hc.1
  have hr := Line.rotation_coordinates w atoms (segmentDirection c.segment)
    (Line.Readout.rail w atoms (capIndex w atoms before))
  have hx := congrArg Prod.fst hr
  have hy := congrArg Prod.snd hr
  dsimp only at hx hy
  change (Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells (Line.Readout.rail w atoms (capIndex w atoms before))).1.val,
    Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells (Line.Readout.rail w atoms (capIndex w atoms before))).2.val) = _
  rw [hx,hy]
  clear hr hx hy
  cases before <;> cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Line.rotatedCoordinates,capIndex,Line.Readout.rail,Line.workY,Line.offsetX,Line.offsetY,
      Line.anchor,Travels,Line.along,Direction.opposite] at * <;>
    apply Prod.ext <;>
    simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,padding] at * <;>
    simp only [hlen] at * <;> omega

end LineCode

namespace TurnCode

def centerSlot (w : ℕ) (c : TurnCode) : Cell (FiniteTools.side w) (FiniteTools.side w) :=
  (Turn.orientation w c.incoming c.outgoing).cells (Turn.center w)

def centerWorld (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) : ℕ × ℕ :=
  (PrimitiveCode.turn c).world w hw (c.centerSlot w)

theorem centerWorld_eq (w : ℕ) (hw : 2 ≤ w) (c : TurnCode) :
    c.centerWorld w hw = (padding w+c.corner.1,padding w+c.corner.2) := by
  change (Turn.offsetX w c.corner+((Turn.orientation w c.incoming c.outgoing).cells (Turn.center w)).1.val,
    Turn.offsetY w c.corner+((Turn.orientation w c.incoming c.outgoing).cells (Turn.center w)).2.val) = _
  rw [Turn.orientation_center]
  apply Prod.ext <;> dsimp [Turn.offsetX,Turn.offsetY,Turn.center,FiniteTools.turnNode,FiniteTools.turnNodePoint] <;>
    unfold FiniteTools.radius padding <;> omega

end TurnCode

theorem JunctionContract.incoming_after_cap (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) : c.capWorld w hw false = t.centerWorld w hw := by
  rw [LineCode.capWorld_eq w hw c H.incoming_good false,TurnCode.centerWorld_eq]
  simp only [Bool.false_eq_true,↓reduceIte,H.incoming_direction,H.incoming_finish]
  have ht := segment_travels c.segment H.incoming_good.1
  rw [H.incoming_direction,H.incoming_finish] at ht
  have hl := H.incoming_good.2.1
  cases hd : t.incoming <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem JunctionContract.outgoing_before_cap (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (t : TurnCode) (d : LineCode)
    (H : JunctionContract w c t d) : d.capWorld w hw true = t.centerWorld w hw := by
  rw [LineCode.capWorld_eq w hw d H.outgoing_good true,TurnCode.centerWorld_eq]
  simp only [↓reduceIte,H.outgoing_direction,H.outgoing_start]
  have ht := segment_travels d.segment H.outgoing_good.1
  rw [H.outgoing_direction,H.outgoing_start] at ht
  have hl := H.outgoing_good.2.1
  cases hd : t.outgoing <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,advance,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

theorem CollinearContract.after_cap_neighbor_rail (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (H : CollinearContract w c d) : c.capWorld w hw false =
      (PrimitiveCode.line d).world w hw (d.railPoint w hw H.next_good 2
        (by have h := H.next_good.2.1; omega)) := by
  rw [LineCode.capWorld_eq w hw c H.first_good false,LineCode.railPoint_world]
  simp only [Bool.false_eq_true,↓reduceIte,H.directions,H.joined]

theorem CollinearContract.before_cap_neighbor_rail (w : ℕ) (hw : 2 ≤ w) (c d : LineCode)
    (H : CollinearContract w c d) : d.capWorld w hw true =
      (PrimitiveCode.line c).world w hw (c.railPoint w hw H.first_good (segmentLength c.segment-1) (by omega)) := by
  rw [LineCode.capWorld_eq w hw d H.next_good true,LineCode.railPoint_world]
  simp only [↓reduceIte,←H.directions,←H.joined]
  have ht := segment_travels c.segment H.first_good.1
  have hl := H.first_good.2.1
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [Travels,Line.along,Direction.opposite] at ht ⊢ <;>
    apply Prod.ext <;> unfold padding <;> omega

end PushPuzzle.PushS.FiniteRouting

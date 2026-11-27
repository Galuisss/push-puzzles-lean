/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingActionGuards
public import PushS.FiniteRoutingPrimitiveGeometry

/-! Every actually used line cell remains in the narrow strip around its literal source segment. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side

namespace LineCode

def actionWorld (w : ℕ) (hw : 2 ≤ w) (c : LineCode)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w)) : ℕ × ℕ :=
  (PrimitiveCode.line c).world w hw
    ((Line.rotation w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) (segmentDirection c.segment)).cells p)

theorem action_footprint (w : ℕ) (hw : 2 ≤ w) (c : LineCode) (hc : LineGood w c.segment)
    (p : Cell (Line.width w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide))) (Line.height w))
    (hp : p ∈ Line.Action.active w (Line.program w (segmentLength c.segment) (c.above != c.desiredSide)) c.above c.last) :
    ∃ u, c.segment.Contains u ∧ Nearby (w+2) (c.actionWorld w hw p) (padding w+u.1,padding w+u.2) := by
  let atoms := Line.program w (segmentLength c.segment) (c.above != c.desiredSide)
  have hu := (Finset.mem_filter.mp hp).2
  have hb := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  change Line.Action.UsedPoint w atoms c.above c.last p at hu
  have hx : FiniteTools.radius w ≤ p.1.val := by
    rcases hu with hu | hu | hu <;> omega
  have hlen : Line.span w atoms = segmentLength c.segment := Line.program_span_of_bound w _ _ hc.2.1
  change FiniteTools.radius w-1 ≤ p.1.val ∧ p.1.val ≤ FiniteTools.radius w+Line.span w atoms+2 ∧
    FiniteTools.radius w-w-1 ≤ p.2.val ∧ p.2.val ≤ FiniteTools.radius w+w+1 ∧ _ at hb
  rw [hlen] at hb
  let n := min (p.1.val-FiniteTools.radius w) (segmentLength c.segment)
  have hn : n ≤ segmentLength c.segment := min_le_right _ _
  have ht := segment_travels c.segment hc.1
  refine ⟨advance (segmentDirection c.segment) c.segment.start n,advance_contains _ _ _ _ n ht hn,?_⟩
  have hr := Line.rotation_coordinates w atoms (segmentDirection c.segment) p
  have hrx := congrArg Prod.fst hr
  have hry := congrArg Prod.snd hr
  dsimp only [coordinates] at hrx hry
  change Nearby (w+2)
    (Line.offsetX w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).1.val,
     Line.offsetY w atoms (segmentDirection c.segment) c.segment.start+
      ((Line.rotation w atoms (segmentDirection c.segment)).cells p).2.val) _
  rw [hrx,hry]
  have hpx := p.1.isLt
  have hpy := p.2.isLt
  cases hd : segmentDirection c.segment <;> simp only [hd] at ht ⊢ <;>
    dsimp [n,Line.rotatedCoordinates,Nearby,advance,Travels,Line.offsetX,Line.offsetY,Line.anchor] at * <;>
    simp only [Line.width,Line.height,FiniteTools.side,FiniteTools.radius,hlen,padding] at * <;> omega

end LineCode
end PushPuzzle.PushS.FiniteRouting

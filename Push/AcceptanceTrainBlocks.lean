/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.TrainDynamics
public import PushS.TwoTrainDynamics
import all PushS.OrderedSlots

/-! Arbitrary unlabelled line trajectories preserve the original separated rigid train blocks. -/

public section
namespace PushPuzzle.Push.AcceptanceTrainBlocks

open PushFS PushS.RowLabels

/-- The three original positive train lengths, with ordered nonoverlapping terminal intervals. -/
structure ThreeCopy (b c : ThreeBlocks) : Prop where
  first_length : c.firstLength = b.firstLength
  middle_length : c.middleLength = b.middleLength
  last_length : c.lastLength = b.lastLength
  separated : c.Separated

/-- The two original positive train lengths, with ordered nonoverlapping terminal intervals. -/
structure TwoCopy (b c : TwoBlocks) : Prop where
  first_length : c.firstLength = b.firstLength
  last_length : c.lastLength = b.lastLength
  separated : c.Separated

private theorem ordered_lift {w h n : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
    {s t : State w h} (slots : Finset ℤ) (hcard : slots.card = n)
    (hsource : (lineBoxes axis lane s).image axis.position = slots)
    (hr : Relation.ReflTransGen (LineAdmissible B cap axis lane) s t) :
    ∃ (S : OrderedLineState n w h axis lane) (T : LineState (Fin n) w h axis lane),
      T.state = t ∧ LineReachable B cap S.toLineState T ∧
        (lineBoxes axis lane S.state).image axis.position = slots := by
  have hc : (lineBoxes axis lane s).card = n :=
    (Finset.card_image_of_injOn (position_injOn axis lane s)).symm.trans ((congrArg Finset.card hsource).trans hcard)
  let S := OrderedLineState.ofState s axis lane hc
  have hS : S.state = s := OrderedLineState.ofState_state _ _ _ _
  obtain ⟨T, ht, hST⟩ := lift_reachable S.toLineState (hS ▸ hr)
  exact ⟨S, T, ht, hST, by rw [hS]; exact hsource⟩

/-- Every real admissible line trajectory preserves three rigid trains, allowing their gaps to close. -/
theorem three_admissible_separated {w h : ℕ} {B : Board w h} {cap : Option ℕ}
    {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hpos : b.Positive) (hb : b.Separated)
    {s t : State w h}
    (hsource : (lineBoxes axis lane s).image axis.position = b.slots)
    (hr : Relation.ReflTransGen (LineAdmissible B cap axis lane) s t) :
    ∃ c, ThreeCopy b c ∧ (lineBoxes axis lane t).image axis.position = c.slots := by
  obtain ⟨S, T, ht, hST, hs⟩ := ordered_lift b.slots (b.card_slots hb) hsource hr
  refine ⟨b.atState hpos T, ⟨rfl, rfl, rfl, b.reachable_separated hb hpos S hST hs⟩, ?_⟩
  simpa only [ht] using b.reachable_slots hb hpos S hST hs

/-- Every real admissible line trajectory preserves two rigid trains, allowing their gap to close. -/
theorem two_admissible_separated {w h : ℕ} {B : Board w h} {cap : Option ℕ}
    {axis : Direction} {lane : ℕ} (b : TwoBlocks) (hpos : b.Positive) (hb : b.Separated)
    {s t : State w h}
    (hsource : (lineBoxes axis lane s).image axis.position = b.slots)
    (hr : Relation.ReflTransGen (LineAdmissible B cap axis lane) s t) :
    ∃ c, TwoCopy b c ∧ (lineBoxes axis lane t).image axis.position = c.slots := by
  obtain ⟨S, T, ht, hST, hs⟩ := ordered_lift b.slots (b.card_slots hb) hsource hr
  refine ⟨b.atState hpos T, ⟨rfl, rfl, b.reachable_separated hb hpos S hST hs⟩, ?_⟩
  simpa only [ht] using b.reachable_slots hb hpos S hST hs

end PushPuzzle.Push.AcceptanceTrainBlocks

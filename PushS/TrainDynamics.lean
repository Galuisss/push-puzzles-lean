/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainRigidity
import all PushS.OrderedSlots

/-! Three rigid trains extracted from an unlabelled admissible line trajectory. -/

public section
namespace PushPuzzle.PushS.RowLabels.ThreeBlocks


open PushFS

/-- Move the three start coordinates while keeping the prescribed lengths. -/
@[expose] def withStarts (b : ThreeBlocks) (first middle last : ℤ) : ThreeBlocks :=
  { b with first := first, middle := middle, last := last }

/-- A placement of the same three fixed-length trains with both internal gaps nonempty. -/
structure RigidCopy (b c : ThreeBlocks) : Prop where
  first_length : c.firstLength = b.firstLength
  middle_length : c.middleLength = b.middleLength
  last_length : c.lastLength = b.lastLength
  gapped : c.Gapped

private theorem lineBoxes_card_of_slots {w h : ℕ} {axis : Direction} {lane : ℕ} (s : State w h)
    (b : ThreeBlocks) (hb : b.Separated)
    (hs : (lineBoxes axis lane s).image axis.position = b.slots) :
    (lineBoxes axis lane s).card = b.size := by
  exact (Finset.card_image_of_injOn (position_injOn axis lane s)).symm.trans
    ((congrArg Finset.card hs).trans (b.card_slots hb))

/-- Initial and target gapped trains force the same three rigid trains at every intermediate line state. -/
theorem admissible_at {w h : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
    (b : ThreeBlocks) (hpos : b.Positive) (hb : b.Gapped) (first middle last : ℤ)
    (hc : (b.withStarts first middle last).Gapped) {s u t : State w h}
    (hpre : Relation.ReflTransGen (LineAdmissible B cap axis lane) s u)
    (hpost : Relation.ReflTransGen (LineAdmissible B cap axis lane) u t)
    (hsource : (lineBoxes axis lane s).image axis.position = b.slots)
    (htarget : (lineBoxes axis lane t).image axis.position = (b.withStarts first middle last).slots) :
    ∃ c, b.RigidCopy c ∧ (lineBoxes axis lane u).image axis.position = c.slots := by
  let c := b.withStarts first middle last
  have hcard := lineBoxes_card_of_slots s b ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hsource
  have htCard := lineBoxes_card_of_slots t c ⟨le_of_lt hc.1, le_of_lt hc.2⟩ htarget
  let S := OrderedLineState.ofState s axis lane hcard
  let U := OrderedLineState.ofState t axis lane htCard
  have hS : S.state = s := OrderedLineState.ofState_state _ _ _ _
  have hU : U.state = t := OrderedLineState.ofState_state _ _ _ _
  rw [← hS] at hpre
  obtain ⟨M, V, hMstate, hVstate, hSM, hMV, _⟩ := S.lift_at U hpre hpost (by rw [hU])
  have hslotsS : (lineBoxes axis lane S.state).image axis.position = b.slots := by rw [hS]; exact hsource
  have hslotsU : (lineBoxes axis lane U.state).image axis.position = c.slots := by rw [hU]; exact htarget
  have hn := c.boundary_nonadjacent hc hpos U hslotsU
  have hgap := b.gapped_at ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S U hSM hMV hslotsS
    (by rw [hVstate, hU]) hn.1 hn.2
  refine ⟨b.atState hpos M, ⟨rfl, rfl, rfl, hgap⟩, ?_⟩
  have hslt := b.reachable_slots ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S hSM hslotsS
  simpa only [hMstate] using hslt

end PushPuzzle.PushS.RowLabels.ThreeBlocks

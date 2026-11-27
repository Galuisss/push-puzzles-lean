/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TwoTrainSlots
import all PushS.OrderedSlots

/-! Two fixed-length box trains remain rigid and unmerged along successful line trajectories. -/

public section
namespace PushPuzzle.PushS.RowLabels.TwoBlocks


open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}

/-- Keep both train lengths and replace their start coordinates. -/
@[expose] def withStarts (b : TwoBlocks) (first last : ℤ) : TwoBlocks := { b with first := first, last := last }

/-- The two marked starts in an arbitrary later line state. -/
@[expose] def atState (b : TwoBlocks) (hb : b.Positive) (T : LineState (Fin b.size) w h axis lane) : TwoBlocks where
  first := axis.position (T.position ⟨0, by dsimp only [size]; obtain ⟨h1, h2⟩ := hb; omega⟩)
  last := axis.position (T.position ⟨b.firstLength, by dsimp only [size]; obtain ⟨h1, h2⟩ := hb; omega⟩)
  firstLength := b.firstLength
  lastLength := b.lastLength

/-- The last first-train label and first last-train label border the unique internal gap. -/
structure BoundarySlots (n : ℕ) where
  firstEnd : Fin n
  lastStart : Fin n

/-- The two boundary labels depend only on the prescribed positive lengths. -/
@[expose] def boundaries (b : TwoBlocks) (hb : b.Positive) : BoundarySlots b.size where
  firstEnd := ⟨b.firstLength - 1, by dsimp only [size]; obtain ⟨h1, h2⟩ := hb; omega⟩
  lastStart := ⟨b.firstLength, by dsimp only [size]; obtain ⟨h1, h2⟩ := hb; omega⟩

/-- Every initial consecutive train remains rigid on the labelled line trajectory. -/
theorem reachable_coordinates (b : TwoBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S : OrderedLineState b.size w h axis lane) {T : LineState (Fin b.size) w h axis lane}
    (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    ∀ i, axis.position (T.position i) = (b.atState hpos T).point i := by
  have hc := b.ordered_coordinates hb S hslots
  have h1 := hpos.1
  have h2 := hpos.2
  have hf := hr.block_offset (start := 0) (len := b.firstLength) (a := b.first) h1
    (by dsimp only [size]; omega) (fun j hj => by
      simpa only [Nat.zero_add] using (hc ⟨j, by dsimp only [size]; omega⟩).trans (b.point_first hj))
  have hl := hr.block_offset (start := b.firstLength) (len := b.lastLength) (a := b.last) h2
    (by dsimp only [size]; omega) (fun j hj => (hc _).trans (b.point_last hj))
  intro i
  have hi := i.isLt
  dsimp only [size] at hi
  by_cases hfirst : i.val < b.firstLength
  · simpa only [Nat.zero_add, atState, point, asThree, ThreeBlocks.point, hfirst, ite_true] using hf i.val hfirst
  · have heq : b.firstLength + (i.val - b.firstLength) = i.val := by omega
    simpa only [heq, atState, point, asThree, ThreeBlocks.point, Nat.add_zero, hfirst, ite_false]
      using hl (i.val - b.firstLength) (by omega)

private theorem reachable_boundaries (b : TwoBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S : OrderedLineState b.size w h axis lane) {T : LineState (Fin b.size) w h axis lane}
    (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    let c := b.atState hpos T
    let cuts := b.boundaries hpos
    axis.position (T.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) ∧
      axis.position (T.position cuts.lastStart) = c.last := by
  have hc := b.reachable_coordinates hb hpos S hr hslots
  have h1 := hpos.1
  exact ⟨(hc _).trans ((b.atState hpos T).point_first (by change b.firstLength - 1 < b.firstLength; omega)), rfl⟩

/-- Strict mark order keeps the two translated trains from overlapping. -/
theorem reachable_separated (b : TwoBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S : OrderedLineState b.size w h axis lane) {T : LineState (Fin b.size) w h axis lane}
    (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) : (b.atState hpos T).Separated := by
  let c := b.atState hpos T
  let cuts := b.boundaries hpos
  obtain ⟨hfe, hls⟩ := reachable_boundaries b hb hpos S hr hslots
  change axis.position (T.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) at hfe
  change axis.position (T.position cuts.lastStart) = c.last at hls
  have h1 := hpos.1
  have ho := hr.strictMono S.ordered (show cuts.firstEnd < cuts.lastStart by change b.firstLength - 1 < b.firstLength; omega)
  change axis.position (T.position cuts.firstEnd) < axis.position (T.position cuts.lastStart) at ho
  change c.first + b.firstLength ≤ c.last
  omega

/-- Every occupied later line coordinate belongs to one of the two translated trains. -/
theorem reachable_slots (b : TwoBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S : OrderedLineState b.size w h axis lane) {T : LineState (Fin b.size) w h axis lane}
    (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    (lineBoxes axis lane T.state).image axis.position = (b.atState hpos T).slots := by
  have hc := b.reachable_coordinates hb hpos S hr hslots
  rw [← T.boxes_image, Finset.image_image, (b.atState hpos T).slots_eq_image_point]
  congr 1
  exact funext hc

/-- Gapped target trains separate their two boundary marks. -/
theorem boundary_nonadjacent (b : TwoBlocks) (hb : b.Gapped) (hpos : b.Positive)
    (U : OrderedLineState b.size w h axis lane)
    (hslots : (lineBoxes axis lane U.state).image axis.position = b.slots) :
    ¬ Adjacent axis (U.position (b.boundaries hpos).firstEnd) (U.position (b.boundaries hpos).lastStart) := by
  let cuts := b.boundaries hpos
  have hc := b.ordered_coordinates (le_of_lt hb) U hslots
  have h1 := hpos.1
  have h2 := hpos.2
  have hfe : axis.position (U.position cuts.firstEnd) = b.first + (b.firstLength - 1 : ℕ) :=
    (hc _).trans (b.point_first (by omega))
  have hls : axis.position (U.position cuts.lastStart) = b.last := by
    change axis.position (U.position ⟨b.firstLength, _⟩) = b.last
    simpa only [Nat.add_zero, Int.natCast_zero, Int.add_zero] using (hc _).trans (b.point_last (show 0 < b.lastLength from h2))
  intro ha
  have he := ha.position
  change axis.position (U.position cuts.lastStart) = axis.position (U.position cuts.firstEnd) + 1 at he
  change b.first + b.firstLength < b.last at hb
  omega

/-- Successful target separation prevents the two trains from merging at an earlier prefix. -/
theorem gapped_at (b : TwoBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S U : OrderedLineState b.size w h axis lane) {M V : LineState (Fin b.size) w h axis lane}
    (hpre : LineReachable B cap S.toLineState M) (hpost : LineReachable B cap M V)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots)
    (hsol : lineBoxes axis lane V.state = lineBoxes axis lane U.state)
    (hgap : ¬ Adjacent axis (U.position (b.boundaries hpos).firstEnd) (U.position (b.boundaries hpos).lastStart)) :
    (b.atState hpos M).Gapped := by
  let c := b.atState hpos M
  let cuts := b.boundaries hpos
  have hsep := b.reachable_separated hb hpos S hpre hslots
  obtain ⟨hfe, hls⟩ := reachable_boundaries b hb hpos S hpre hslots
  change axis.position (M.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) at hfe
  change axis.position (M.position cuts.lastStart) = c.last at hls
  have hn := S.nonadjacent_at hpre hpost hsol cuts.firstEnd cuts.lastStart hgap
  have h1 := hpos.1
  change c.first + b.firstLength < c.last
  by_contra hbad
  apply hn
  apply (adjacent_iff_coordinates axis _ _).mpr
  refine ⟨(M.position_lane _).trans (M.position_lane _).symm, ?_⟩
  change c.first + b.firstLength ≤ c.last at hsep
  omega

/-- A placement of the same two fixed-length trains with their internal gap nonempty. -/
structure RigidCopy (b c : TwoBlocks) : Prop where
  first_length : c.firstLength = b.firstLength
  last_length : c.lastLength = b.lastLength
  gapped : c.Gapped

/-- Unlabelled admissible trajectories recover the two genuine rigid unmerged trains at each prefix. -/
theorem admissible_at (b : TwoBlocks) (hpos : b.Positive) (hb : b.Gapped) (first last : ℤ)
    (hc : (b.withStarts first last).Gapped) {s u t : State w h}
    (hpre : Relation.ReflTransGen (LineAdmissible B cap axis lane) s u)
    (hpost : Relation.ReflTransGen (LineAdmissible B cap axis lane) u t)
    (hsource : (lineBoxes axis lane s).image axis.position = b.slots)
    (htarget : (lineBoxes axis lane t).image axis.position = (b.withStarts first last).slots) :
    ∃ c, b.RigidCopy c ∧ (lineBoxes axis lane u).image axis.position = c.slots := by
  let c := b.withStarts first last
  have hcard := (Finset.card_image_of_injOn (position_injOn axis lane s)).symm.trans
    ((congrArg Finset.card hsource).trans (b.card_slots (le_of_lt hb)))
  have htCard := (Finset.card_image_of_injOn (position_injOn axis lane t)).symm.trans
    ((congrArg Finset.card htarget).trans (c.card_slots (le_of_lt hc)))
  let S := OrderedLineState.ofState s axis lane hcard
  let U := OrderedLineState.ofState t axis lane htCard
  have hS : S.state = s := OrderedLineState.ofState_state _ _ _ _
  have hU : U.state = t := OrderedLineState.ofState_state _ _ _ _
  rw [← hS] at hpre
  obtain ⟨M, V, hMstate, hVstate, hSM, hMV, _⟩ := S.lift_at U hpre hpost (by rw [hU])
  have hslt : (lineBoxes axis lane S.state).image axis.position = b.slots := by rw [hS]; exact hsource
  have htlt : (lineBoxes axis lane U.state).image axis.position = c.slots := by rw [hU]; exact htarget
  have hn := c.boundary_nonadjacent hc hpos U htlt
  have hgap := b.gapped_at (le_of_lt hb) hpos S U hSM hMV hslt (by rw [hVstate, hU]) hn
  refine ⟨b.atState hpos M, ⟨rfl, rfl, hgap⟩, ?_⟩
  have hcoord := b.reachable_slots (le_of_lt hb) hpos S hSM hslt
  simpa only [hMstate] using hcoord

end PushPuzzle.PushS.RowLabels.TwoBlocks

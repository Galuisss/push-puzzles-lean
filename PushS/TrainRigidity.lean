/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainSlots

/-! Occupancy marks keep every initial consecutive train rigid along the complete line trajectory. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

variable {w h n : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
  {S T : LineState (Fin n) w h axis lane}

/-- Every initially consecutive label block remains a rigid train of its prescribed length. -/
theorem LineReachable.block_offset (hr : LineReachable B cap S T) {start len : ℕ} {a : ℤ}
    (hlen : 0 < len) (hbound : start + len ≤ n)
    (hsource : ∀ j, (hj : j < len) → axis.position (S.position ⟨start + j, by omega⟩) = a + j) :
    ∀ j, (hj : j < len) →
      axis.position (T.position ⟨start + j, by omega⟩) =
        axis.position (T.position ⟨start, by omega⟩) + j := by
  intro j
  induction j with
  | zero => intro hj; simp only [Nat.add_zero, Int.natCast_zero, Int.add_zero]
  | succ j ih =>
    intro hj
    have hprev : j < len := by omega
    have hadj : Adjacent axis (S.position ⟨start + j, by omega⟩)
        (S.position ⟨start + (j + 1), by omega⟩) := by
      apply (adjacent_iff_coordinates axis _ _).mpr
      refine ⟨(S.position_lane _).trans (S.position_lane _).symm, ?_⟩
      rw [hsource j hprev, hsource (j + 1) hj]
      omega
    have htarget := (hr.adjacent _ _ hadj).position
    rw [ih hprev] at htarget
    exact htarget.trans (by omega)

namespace ThreeBlocks

/-- All three marked trains contain a box. -/
@[expose] def Positive (b : ThreeBlocks) : Prop :=
  0 < b.firstLength ∧ 0 < b.middleLength ∧ 0 < b.lastLength

/-- The four occupancy marks bordering the two internal gaps. -/
structure BoundarySlots (n : ℕ) where
  firstEnd : Fin n
  middleStart : Fin n
  middleEnd : Fin n
  lastStart : Fin n

/-- The boundary labels depend only on the three prescribed train lengths. -/
@[expose] def boundaries (b : ThreeBlocks) (hb : b.Positive) : BoundarySlots b.size where
  firstEnd := ⟨b.firstLength - 1, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩
  middleStart := ⟨b.firstLength, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩
  middleEnd := ⟨b.firstLength + (b.middleLength - 1), by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩
  lastStart := ⟨b.firstLength + b.middleLength, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩

/-- Both internal gaps contain at least one unoccupied coordinate. -/
@[expose] def Gapped (b : ThreeBlocks) : Prop :=
  b.first + b.firstLength < b.middle ∧ b.middle + b.middleLength < b.last

/-- Place the same three train lengths at their first marked positions in a new line state. -/
@[expose] def atState {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Positive)
    (T : LineState (Fin b.size) w h axis lane) : ThreeBlocks where
  first := axis.position (T.position ⟨0, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩)
  middle := axis.position (T.position ⟨b.firstLength, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩)
  last := axis.position (T.position ⟨b.firstLength + b.middleLength, by dsimp only [size]; obtain ⟨h1, h2, h3⟩ := hb; omega⟩)
  firstLength := b.firstLength
  middleLength := b.middleLength
  lastLength := b.lastLength

/-- First-block coordinates in the canonical enumeration. -/
theorem point_first (b : ThreeBlocks) {j : ℕ} (hj : j < b.firstLength) :
    b.point ⟨j, by dsimp only [size]; omega⟩ = b.first + j := by
  simp only [point, hj, ite_true]

/-- Middle-block coordinates in the canonical enumeration. -/
theorem point_middle (b : ThreeBlocks) {j : ℕ} (hj : j < b.middleLength) :
    b.point ⟨b.firstLength + j, by dsimp only [size]; omega⟩ = b.middle + j := by
  simp only [point]
  split_ifs <;> omega

/-- Last-block coordinates in the canonical enumeration. -/
theorem point_last (b : ThreeBlocks) {j : ℕ} (hj : j < b.lastLength) :
    b.point ⟨b.firstLength + b.middleLength + j, by dsimp only [size]; omega⟩ = b.last + j := by
  simp only [point]
  split_ifs <;> omega

/-- Ordered slots of gapped target trains separate the two pairs of boundary marks. -/
theorem boundary_nonadjacent {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Gapped)
    (hpos : b.Positive) (U : OrderedLineState b.size w h axis lane)
    (hslots : (lineBoxes axis lane U.state).image axis.position = b.slots) :
    ¬ Adjacent axis (U.position (b.boundaries hpos).firstEnd) (U.position (b.boundaries hpos).middleStart) ∧
      ¬ Adjacent axis (U.position (b.boundaries hpos).middleEnd) (U.position (b.boundaries hpos).lastStart) := by
  let cuts := b.boundaries hpos
  have hc := b.ordered_coordinates ⟨le_of_lt hb.1, le_of_lt hb.2⟩ U hslots
  have h1 := hpos.1
  have h2 := hpos.2.1
  have h3 := hpos.2.2
  have hfe : axis.position (U.position cuts.firstEnd) = b.first + (b.firstLength - 1 : ℕ) :=
    (hc _).trans (b.point_first (by omega))
  have hms : axis.position (U.position cuts.middleStart) = b.middle := by
    change axis.position (U.position ⟨b.firstLength, _⟩) = b.middle
    simpa only [Nat.add_zero, Int.natCast_zero, Int.add_zero] using (hc _).trans (b.point_middle (show 0 < b.middleLength from h2))
  have hme : axis.position (U.position cuts.middleEnd) = b.middle + (b.middleLength - 1 : ℕ) :=
    (hc _).trans (b.point_middle (by omega))
  have hls : axis.position (U.position cuts.lastStart) = b.last := by
    change axis.position (U.position ⟨b.firstLength + b.middleLength, _⟩) = b.last
    simpa only [Nat.add_zero, Int.natCast_zero, Int.add_zero] using (hc _).trans (b.point_last (show 0 < b.lastLength from h3))
  constructor
  · intro ha
    have he := ha.position
    change axis.position (U.position cuts.middleStart) = axis.position (U.position cuts.firstEnd) + 1 at he
    have hg := hb.1
    omega
  · intro ha
    have he := ha.position
    change axis.position (U.position cuts.lastStart) = axis.position (U.position cuts.middleEnd) + 1 at he
    have hg := hb.2
    omega

/-- The original three box trains remain three rigid ordered blocks on the labelled trajectory. -/
theorem reachable_coordinates {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Separated)
    (hpos : b.Positive) (S : OrderedLineState b.size w h axis lane)
    {T : LineState (Fin b.size) w h axis lane} (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    ∀ i : Fin b.size, axis.position (T.position i) = (b.atState hpos T).point i := by
  have hsource := b.ordered_coordinates hb S hslots
  obtain ⟨h1, h2, h3⟩ := hpos
  have hf := hr.block_offset (start := 0) (len := b.firstLength) (a := b.first) h1
    (by dsimp only [size]; omega) (fun j hj => by
      simpa only [Nat.zero_add] using (hsource ⟨j, by dsimp only [size]; omega⟩).trans (b.point_first hj))
  have hm := hr.block_offset (start := b.firstLength) (len := b.middleLength) (a := b.middle) h2
    (by dsimp only [size]; omega) (fun j hj => by rw [hsource, b.point_middle hj])
  have hl := hr.block_offset (start := b.firstLength + b.middleLength) (len := b.lastLength) (a := b.last) h3
    (by dsimp only [size]; omega) (fun j hj => by rw [hsource, b.point_last hj])
  intro i
  have hi := i.isLt
  dsimp only [size] at hi
  by_cases hfirst : i.val < b.firstLength
  · simpa only [Nat.zero_add, atState, point, hfirst, ite_true] using hf i.val hfirst
  · by_cases hmiddle : i.val < b.firstLength + b.middleLength
    · have heq : b.firstLength + (i.val - b.firstLength) = i.val := by omega
      simpa only [heq, atState, point, hfirst, ite_false, hmiddle, ite_true] using hm (i.val - b.firstLength) (by omega)
    · have heq : b.firstLength + b.middleLength + (i.val - (b.firstLength + b.middleLength)) = i.val := by omega
      simpa only [heq, atState, point, hfirst, ite_false, hmiddle] using hl (i.val - (b.firstLength + b.middleLength)) (by omega)

private theorem reachable_boundaries {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Separated)
    (hpos : b.Positive) (S : OrderedLineState b.size w h axis lane)
    {T : LineState (Fin b.size) w h axis lane} (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    let c := b.atState hpos T
    let cuts := b.boundaries hpos
    axis.position (T.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) ∧
      axis.position (T.position cuts.middleStart) = c.middle ∧
      axis.position (T.position cuts.middleEnd) = c.middle + (b.middleLength - 1 : ℕ) ∧
      axis.position (T.position cuts.lastStart) = c.last := by
  let c := b.atState hpos T
  let cuts := b.boundaries hpos
  have hc := b.reachable_coordinates hb hpos S hr hslots
  obtain ⟨h1, h2, h3⟩ := hpos
  have hfe : axis.position (T.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) :=
    (hc _).trans (c.point_first (by change b.firstLength - 1 < b.firstLength; omega))
  have hms : axis.position (T.position cuts.middleStart) = c.middle := rfl
  have hme : axis.position (T.position cuts.middleEnd) = c.middle + (b.middleLength - 1 : ℕ) :=
    (hc _).trans (c.point_middle (by change b.middleLength - 1 < b.middleLength; omega))
  have hls : axis.position (T.position cuts.lastStart) = c.last := rfl
  exact ⟨hfe, hms, hme, hls⟩

/-- Mark order prevents the three rigid trains from overlapping at any intermediate state. -/
theorem reachable_separated {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Separated)
    (hpos : b.Positive) (S : OrderedLineState b.size w h axis lane)
    {T : LineState (Fin b.size) w h axis lane} (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    (b.atState hpos T).Separated := by
  let c := b.atState hpos T
  let cuts := b.boundaries hpos
  obtain ⟨hfe, hms, hme, hls⟩ := reachable_boundaries b hb hpos S hr hslots
  change axis.position (T.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) at hfe
  change axis.position (T.position cuts.middleStart) = c.middle at hms
  change axis.position (T.position cuts.middleEnd) = c.middle + (b.middleLength - 1 : ℕ) at hme
  change axis.position (T.position cuts.lastStart) = c.last at hls
  obtain ⟨h1, h2, h3⟩ := hpos
  have hmono := hr.strictMono S.ordered
  have ho1 := hmono (show cuts.firstEnd < cuts.middleStart by change b.firstLength - 1 < b.firstLength; omega)
  have ho2 := hmono (show cuts.middleEnd < cuts.lastStart by change b.firstLength + (b.middleLength - 1) < b.firstLength + b.middleLength; omega)
  change axis.position (T.position cuts.firstEnd) < axis.position (T.position cuts.middleStart) at ho1
  change axis.position (T.position cuts.middleEnd) < axis.position (T.position cuts.lastStart) at ho2
  change c.first + b.firstLength ≤ c.middle ∧ c.middle + b.middleLength ≤ c.last
  omega

/-- The three translated trains describe every occupied coordinate of the actual labelled state. -/
theorem reachable_slots {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Separated)
    (hpos : b.Positive) (S : OrderedLineState b.size w h axis lane)
    {T : LineState (Fin b.size) w h axis lane} (hr : LineReachable B cap S.toLineState T)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots) :
    (lineBoxes axis lane T.state).image axis.position = (b.atState hpos T).slots := by
  have hc := b.reachable_coordinates hb hpos S hr hslots
  rw [← T.boxes_image, Finset.image_image, (b.atState hpos T).slots_eq_image_point]
  congr 1
  exact funext hc

/-- Target-separated trains never merge at an earlier successful state. -/
theorem gapped_at {axis : Direction} {lane : ℕ} (b : ThreeBlocks) (hb : b.Separated) (hpos : b.Positive)
    (S U : OrderedLineState b.size w h axis lane) {M V : LineState (Fin b.size) w h axis lane}
    (hpre : LineReachable B cap S.toLineState M) (hpost : LineReachable B cap M V)
    (hslots : (lineBoxes axis lane S.state).image axis.position = b.slots)
    (hsol : lineBoxes axis lane V.state = lineBoxes axis lane U.state)
    (hfirst : ¬ Adjacent axis (U.position (b.boundaries hpos).firstEnd) (U.position (b.boundaries hpos).middleStart))
    (hmiddle : ¬ Adjacent axis (U.position (b.boundaries hpos).middleEnd) (U.position (b.boundaries hpos).lastStart)) :
    (b.atState hpos M).Gapped := by
  let c := b.atState hpos M
  let cuts := b.boundaries hpos
  have hsep := b.reachable_separated hb hpos S hpre hslots
  obtain ⟨hfe, hms, hme, hls⟩ := reachable_boundaries b hb hpos S hpre hslots
  change axis.position (M.position cuts.firstEnd) = c.first + (b.firstLength - 1 : ℕ) at hfe
  change axis.position (M.position cuts.middleStart) = c.middle at hms
  change axis.position (M.position cuts.middleEnd) = c.middle + (b.middleLength - 1 : ℕ) at hme
  change axis.position (M.position cuts.lastStart) = c.last at hls
  obtain ⟨h1, h2, h3⟩ := hpos
  have hn1 := S.nonadjacent_at hpre hpost hsol cuts.firstEnd cuts.middleStart hfirst
  have hn2 := S.nonadjacent_at hpre hpost hsol cuts.middleEnd cuts.lastStart hmiddle
  change c.first + b.firstLength < c.middle ∧ c.middle + b.middleLength < c.last
  constructor
  · by_contra hbad
    apply hn1
    apply (adjacent_iff_coordinates axis _ _).mpr
    refine ⟨(M.position_lane _).trans (M.position_lane _).symm, ?_⟩
    have hs := hsep.1
    change c.first + b.firstLength ≤ c.middle at hs
    omega
  · by_contra hbad
    apply hn2
    apply (adjacent_iff_coordinates axis _ _).mpr
    refine ⟨(M.position_lane _).trans (M.position_lane _).symm, ?_⟩
    have hs := hsep.2
    change c.middle + b.middleLength ≤ c.last at hs
    omega

end ThreeBlocks
end PushPuzzle.PushS.RowLabels

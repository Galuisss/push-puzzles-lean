/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainDynamics
public import PushS.LineForcing

/-! Consistent rigid-train marks across one actual successful step and their exact forcing gaps. -/

public section
namespace PushPuzzle.PushS.RowLabels.ThreeBlocks


open PushFS

variable {w h : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}

/-- One actual step with the same train-boundary marks and both complete gapped train layouts. -/
structure MarkedStep (b : ThreeBlocks) (hpos : b.Positive) (B : Board w h) (cap : Option ℕ)
    (axis : Direction) (lane : ℕ) (u v : State w h) where
  before : LineState (Fin b.size) w h axis lane
  after : LineState (Fin b.size) w h axis lane
  before_state : before.state = u
  after_state : after.state = v
  step : LineStep B cap before after
  before_coordinates (i : Fin b.size) : axis.position (before.position i) = (b.atState hpos before).point i
  after_coordinates (i : Fin b.size) : axis.position (after.position i) = (b.atState hpos after).point i
  before_gapped : (b.atState hpos before).Gapped
  after_gapped : (b.atState hpos after).Gapped
  before_slots : (lineBoxes axis lane before.state).image axis.position = (b.atState hpos before).slots
  after_slots : (lineBoxes axis lane after.state).image axis.position = (b.atState hpos after).slots

/-- A successful unlabelled line step has consistent original rigid-train marks on both sides. -/
theorem admissible_step (b : ThreeBlocks) (hpos : b.Positive) (hb : b.Gapped) (first middle last : ℤ)
    (hc : (b.withStarts first middle last).Gapped) {s u v t : State w h}
    (hpre : Relation.ReflTransGen (LineAdmissible B cap axis lane) s u)
    (hstep : LineAdmissible B cap axis lane u v)
    (hpost : Relation.ReflTransGen (LineAdmissible B cap axis lane) v t)
    (hsource : (lineBoxes axis lane s).image axis.position = b.slots)
    (htarget : (lineBoxes axis lane t).image axis.position = (b.withStarts first middle last).slots) :
    Nonempty (MarkedStep b hpos B cap axis lane u v) := by
  let c := b.withStarts first middle last
  have hcard := (Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact axis.cell_ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he)).symm.trans
    ((congrArg Finset.card hsource).trans (b.card_slots ⟨le_of_lt hb.1, le_of_lt hb.2⟩))
  have htCard := (Finset.card_image_of_injOn (by
    intro p hp q hq he
    exact axis.cell_ext ((Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hq).2.symm) he)).symm.trans
    ((congrArg Finset.card htarget).trans (c.card_slots ⟨le_of_lt hc.1, le_of_lt hc.2⟩))
  let S := OrderedLineState.ofState s axis lane hcard
  let U := OrderedLineState.ofState t axis lane htCard
  have hS : S.state = s := OrderedLineState.ofState_state _ _ _ _
  have hU : U.state = t := OrderedLineState.ofState_state _ _ _ _
  rw [← hS] at hpre
  obtain ⟨M, N, V, hM, hN, hV, hSM, hMN, hNV, _⟩ := S.lift_step_at U hpre hstep hpost (by rw [hU])
  have hslt : (lineBoxes axis lane S.state).image axis.position = b.slots := by rw [hS]; exact hsource
  have htlt : (lineBoxes axis lane U.state).image axis.position = c.slots := by rw [hU]; exact htarget
  have hn := c.boundary_nonadjacent hc hpos U htlt
  have hMgap := b.gapped_at ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S U hSM
    ((Relation.ReflTransGen.single hMN).trans hNV) hslt (by rw [hV, hU]) hn.1 hn.2
  have hNgap := b.gapped_at ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S U (hSM.tail hMN)
    hNV hslt (by rw [hV, hU]) hn.1 hn.2
  exact ⟨⟨M, N, hM, hN, hMN,
    b.reachable_coordinates ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S hSM hslt,
    b.reachable_coordinates ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S (hSM.tail hMN) hslt,
    hMgap, hNgap,
    b.reachable_slots ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S hSM hslt,
    b.reachable_slots ⟨le_of_lt hb.1, le_of_lt hb.2⟩ hpos S (hSM.tail hMN) hslt⟩⟩

namespace MarkedStep

variable {b : ThreeBlocks} {hpos : b.Positive} {u v : State w h}
  (m : MarkedStep b hpos B cap axis lane u v)

/-- The three genuine train starts before the step. -/
@[expose] def beforeBlocks : ThreeBlocks := b.atState hpos m.before

/-- The three genuine train starts after the step. -/
@[expose] def afterBlocks : ThreeBlocks := b.atState hpos m.after

private theorem force_start (i : Fin b.size) {x y : ℤ}
    (hx : axis.position (m.before.position i) = x) (hy : axis.position (m.after.position i) = y)
    (hi : x < y) (hhole : x - 1 ∉ m.beforeBlocks.slots) : axis.position u.player = x - 1 := by
  have hgap : axis.position (m.before.position i) - 1 ∉ (lineBoxes axis lane m.before.state).image axis.position := by
    rw [m.before_slots, hx]
    exact hhole
  have ha := m.step.force_along i (by rw [hx, hy]; exact hi) (m.before.no_box_behind_coordinate i hgap)
  have hp := ha.position
  rw [hx, m.before_state] at hp
  omega

private theorem force_end (i : Fin b.size) {x y : ℤ}
    (hx : axis.position (m.before.position i) = x) (hy : axis.position (m.after.position i) = y)
    (hi : y < x) (hhole : x + 1 ∉ m.beforeBlocks.slots) : axis.position u.player = x + 1 := by
  have hgap : axis.position (m.before.position i) + 1 ∉ (lineBoxes axis lane m.before.state).image axis.position := by
    rw [m.before_slots, hx]
    exact hhole
  have ha := m.step.force_against i (by rw [hx, hy]; exact hi) (m.before.no_box_ahead_coordinate i hgap)
  have ha' : Adjacent axis (m.before.position i) m.before.state.player := by
    simpa only [Direction.opposite_opposite] using ha.reverse
  simpa only [hx, m.before_state] using ha'.position

/-- Any actual train displacement places the player on this same rail. -/
theorem player_lane (hi : m.beforeBlocks.first ≠ m.afterBlocks.first ∨
    m.beforeBlocks.middle ≠ m.afterBlocks.middle ∨ m.beforeBlocks.last ≠ m.afterBlocks.last) :
    axis.lane u.player = lane := by
  have hf : ∃ i : Fin b.size, m.after.position i ≠ m.before.position i := by
    rcases hi with hi | hi | hi
    · refine ⟨⟨0, by dsimp only [size]; have h := hpos.1; omega⟩, ?_⟩
      intro he
      apply hi
      exact (congrArg axis.position he).symm
    · refine ⟨⟨b.firstLength, by dsimp only [size]; have h := hpos.2.1; omega⟩, ?_⟩
      intro he
      apply hi
      exact (congrArg axis.position he).symm
    · refine ⟨⟨b.firstLength + b.middleLength, by dsimp only [size]; have h := hpos.2.2; omega⟩, ?_⟩
      intro he
      apply hi
      exact (congrArg axis.position he).symm
  obtain ⟨i, hi⟩ := hf
  simpa only [m.before_state] using m.step.player_lane_of_changed i hi

/-- Moving the first train forward requires its preceding outer gap. -/
theorem first_forward (hi : m.beforeBlocks.first < m.afterBlocks.first) :
    axis.position u.player = m.beforeBlocks.first - 1 := by
  apply m.force_start (x := m.beforeBlocks.first) (y := m.afterBlocks.first)
    ⟨0, by dsimp only [size]; have h := hpos.1; omega⟩ rfl rfl hi
  rw [mem_slots]
  have hg := m.before_gapped
  simp only [beforeBlocks, atState, Gapped] at hg ⊢
  omega

/-- Moving the middle train forward requires its preceding internal gap. -/
theorem middle_forward (hi : m.beforeBlocks.middle < m.afterBlocks.middle) :
    axis.position u.player = m.beforeBlocks.middle - 1 := by
  apply m.force_start (x := m.beforeBlocks.middle) (y := m.afterBlocks.middle)
    ⟨b.firstLength, by dsimp only [size]; have h := hpos.2.1; omega⟩ rfl rfl hi
  rw [mem_slots]
  have hg := m.before_gapped
  simp only [beforeBlocks, atState, Gapped] at hg ⊢
  omega

/-- Moving the last train forward requires its preceding internal gap. -/
theorem last_forward (hi : m.beforeBlocks.last < m.afterBlocks.last) :
    axis.position u.player = m.beforeBlocks.last - 1 := by
  apply m.force_start (x := m.beforeBlocks.last) (y := m.afterBlocks.last)
    ⟨b.firstLength + b.middleLength, by dsimp only [size]; have h := hpos.2.2; omega⟩ rfl rfl hi
  rw [mem_slots]
  have hg := m.before_gapped
  simp only [beforeBlocks, atState, Gapped] at hg ⊢
  omega

/-- Moving the first train backward requires its following internal gap. -/
theorem first_backward (hi : m.afterBlocks.first < m.beforeBlocks.first) :
    axis.position u.player = m.beforeBlocks.first + b.firstLength := by
  have h1 := hpos.1
  let i : Fin b.size := ⟨b.firstLength - 1, by dsimp only [size]; omega⟩
  have hs : axis.position (m.before.position i) = m.beforeBlocks.first + (b.firstLength - 1 : ℕ) :=
    (m.before_coordinates i).trans (m.beforeBlocks.point_first (by change b.firstLength - 1 < b.firstLength; omega))
  have ht : axis.position (m.after.position i) = m.afterBlocks.first + (b.firstLength - 1 : ℕ) :=
    (m.after_coordinates i).trans (m.afterBlocks.point_first (by change b.firstLength - 1 < b.firstLength; omega))
  have hf := m.force_end i hs ht (by omega) (by
    rw [mem_slots]
    have hg := m.before_gapped
    simp only [beforeBlocks, atState, Gapped] at hg ⊢
    omega)
  omega

/-- Moving the middle train backward requires its following internal gap. -/
theorem middle_backward (hi : m.afterBlocks.middle < m.beforeBlocks.middle) :
    axis.position u.player = m.beforeBlocks.middle + b.middleLength := by
  have h2 := hpos.2.1
  let i : Fin b.size := ⟨b.firstLength + (b.middleLength - 1), by dsimp only [size]; omega⟩
  have hs : axis.position (m.before.position i) = m.beforeBlocks.middle + (b.middleLength - 1 : ℕ) :=
    (m.before_coordinates i).trans (m.beforeBlocks.point_middle (by change b.middleLength - 1 < b.middleLength; omega))
  have ht : axis.position (m.after.position i) = m.afterBlocks.middle + (b.middleLength - 1 : ℕ) :=
    (m.after_coordinates i).trans (m.afterBlocks.point_middle (by change b.middleLength - 1 < b.middleLength; omega))
  have hf := m.force_end i hs ht (by omega) (by
    rw [mem_slots]
    have hg := m.before_gapped
    simp only [beforeBlocks, atState, Gapped] at hg ⊢
    omega)
  omega

/-- Moving the last train backward requires its following outer gap. -/
theorem last_backward (hi : m.afterBlocks.last < m.beforeBlocks.last) :
    axis.position u.player = m.beforeBlocks.last + b.lastLength := by
  have h3 := hpos.2.2
  let i : Fin b.size := ⟨b.firstLength + b.middleLength + (b.lastLength - 1), by dsimp only [size]; omega⟩
  have hs : axis.position (m.before.position i) = m.beforeBlocks.last + (b.lastLength - 1 : ℕ) :=
    (m.before_coordinates i).trans (m.beforeBlocks.point_last (by change b.lastLength - 1 < b.lastLength; omega))
  have ht : axis.position (m.after.position i) = m.afterBlocks.last + (b.lastLength - 1 : ℕ) :=
    (m.after_coordinates i).trans (m.afterBlocks.point_last (by change b.lastLength - 1 < b.lastLength; omega))
  have hf := m.force_end i hs ht (by omega) (by
    rw [mem_slots]
    have hg := m.before_gapped
    simp only [beforeBlocks, atState, Gapped] at hg ⊢
    omega)
  omega

end MarkedStep
end PushPuzzle.PushS.RowLabels.ThreeBlocks

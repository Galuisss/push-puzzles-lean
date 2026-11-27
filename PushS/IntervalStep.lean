/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.TrainInterval
public import PushS.LineForcing
import all PushS.TrainInterval
import all PushS.OrderedSlots

/-! Actual one-step dynamics and forcing sides of one complete fixed-length train. -/

public section
namespace PushPuzzle.PushS.RowLabels


open PushFS

/-- One actual line step with the same complete consecutive train marked before and after. -/
structure IntervalMarkedStep {w h : ℕ} (B : Board w h) (cap : Option ℕ) (axis : Direction) (lane len : ℕ)
    (s t : State w h) (first next : ℤ) where
  length_pos : 0 < len
  source : LineState (Fin len) w h axis lane
  target : LineState (Fin len) w h axis lane
  source_state : source.state = s
  target_state : target.state = t
  step : LineStep B cap source target
  source_coordinates (i : Fin len) : axis.position (source.position i) = first + i.val
  target_coordinates (i : Fin len) : axis.position (target.position i) = next + i.val

/-- Exact source and target interval slots lift the original step with all literal train coordinates. -/
theorem interval_marked_step {w h len : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
    {s t : State w h} {first next : ℤ} (hlen : 0 < len) (hm : LineAdmissible B cap axis lane s t)
    (hsource : (lineBoxes axis lane s).image axis.position = Finset.Ico first (first + len))
    (htarget : (lineBoxes axis lane t).image axis.position = Finset.Ico next (next + len)) :
    Nonempty (IntervalMarkedStep B cap axis lane len s t first next) := by
  have hcard (v : State w h) (a : ℤ)
      (hslots : (lineBoxes axis lane v).image axis.position = Finset.Ico a (a + len)) :
      (lineBoxes axis lane v).card = len :=
    (Finset.card_image_of_injOn (position_injOn axis lane v)).symm.trans
      ((congrArg Finset.card hslots).trans (interval_card a len))
  obtain ⟨S, hS⟩ : ∃ S : OrderedLineState len w h axis lane, S.state = s :=
    ⟨OrderedLineState.ofState s axis lane (hcard s first hsource), OrderedLineState.ofState_state _ _ _ _⟩
  obtain ⟨U, hU⟩ : ∃ U : OrderedLineState len w h axis lane, U.state = t :=
    ⟨OrderedLineState.ofState t axis lane (hcard t next htarget), OrderedLineState.ofState_state _ _ _ _⟩
  obtain ⟨T, hT, hstep⟩ := lift_step S.toLineState (hS.symm ▸ hm)
  have hmatch := OrderedLineState.matches_target (S := S) (U := U) (.single hstep) (by rw [hT, hU])
  refine ⟨⟨hlen, S.toLineState, T, hS, hT, hstep,
    S.interval_coordinates first (by rw [hS]; exact hsource), ?_⟩⟩
  intro i
  rw [hmatch]
  exact U.interval_coordinates next (by rw [hU]; exact htarget) i

namespace IntervalMarkedStep

variable {w h len : ℕ} {B : Board w h} {cap : Option ℕ} {axis : Direction} {lane : ℕ}
  {s t : State w h} {first next : ℤ} (hs : IntervalMarkedStep B cap axis lane len s t first next)

include hs

/-- The complete train translates by at most one coordinate in one actual step. -/
theorem start_bounds : first - 1 ≤ next ∧ next ≤ first + 1 := by
  have hb := hs.step.coordinate_bounds ⟨0, hs.length_pos⟩
  simpa only [hs.source_coordinates, hs.target_coordinates, Int.natCast_zero, Int.add_zero] using hb

private theorem marked_box (q : Cell w h) (hqlane : axis.lane q = lane) (hq : q ∈ hs.source.state.boxes) :
    ∃ i : Fin len, axis.position q = first + i.val := by
  have hqline : q ∈ lineBoxes axis lane hs.source.state := Finset.mem_filter.mpr ⟨hq, hqlane⟩
  rw [← hs.source.boxes_image] at hqline
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hqline
  exact ⟨i, (congrArg axis.position hi.symm).trans (hs.source_coordinates i)⟩

/-- Increasing the complete train's start requires the real player immediately before its first box. -/
theorem force_increase (hi : first < next) : axis.position s.player = first - 1 ∧ axis.lane s.player = lane := by
  let i : Fin len := ⟨0, hs.length_pos⟩
  have h0 : axis.position (hs.source.position i) = first := by simpa only [i, Int.natCast_zero, Int.add_zero] using hs.source_coordinates i
  have h1 : axis.position (hs.target.position i) = next := by simpa only [i, Int.natCast_zero, Int.add_zero] using hs.target_coordinates i
  have hforce := hs.step.force_along i (by rw [h0, h1]; exact hi) (by
    intro q ha hq
    have hqlane : axis.lane q = lane := ha.lane.symm.trans (hs.source.position_lane i)
    obtain ⟨j, hj⟩ := hs.marked_box q hqlane hq
    have hp := ha.position
    rw [h0, hj] at hp
    omega)
  have hp := hforce.position
  have hlane := hforce.lane.symm.trans (hs.source.position_lane i)
  rw [hs.source_state] at hp hlane
  exact ⟨by omega, hlane⟩

/-- Decreasing the complete train's start requires the real player immediately after its last box. -/
theorem force_decrease (hi : next < first) : axis.position s.player = first + len ∧ axis.lane s.player = lane := by
  let i : Fin len := ⟨len - 1, by have h := hs.length_pos; omega⟩
  have h0 := hs.source_coordinates i
  have h1 := hs.target_coordinates i
  have hforce := hs.step.force_against i (by rw [h0, h1]; omega) (by
    intro q ha hq
    have har : Adjacent axis (hs.source.position i) q := by simpa only [Direction.opposite_opposite] using ha.reverse
    have hqlane : axis.lane q = lane := har.lane.trans (hs.source.position_lane i)
    obtain ⟨j, hj⟩ := hs.marked_box q hqlane hq
    have hp := har.position
    rw [h0, hj] at hp
    have hjlt := j.isLt
    change first + j.val = first + (len - 1 : ℕ) + 1 at hp
    have hlen := hs.length_pos
    omega)
  have har : Adjacent axis (hs.source.position i) hs.source.state.player := by
    simpa only [Direction.opposite_opposite] using hforce.reverse
  have hp := har.position
  have hlane := har.lane.trans (hs.source.position_lane i)
  rw [hs.source_state] at hp hlane
  have hlen := hs.length_pos
  have h0' : axis.position (hs.source.position i) = first + (len - 1 : ℕ) := h0
  exact ⟨by omega, hlane⟩

end IntervalMarkedStep
end PushPuzzle.PushS.RowLabels

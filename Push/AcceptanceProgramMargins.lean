/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramLayout
public import PushS.PortSignalLocality
public import PushS.PortCentralMargins
import all Push.AcceptanceProgramLayout

/-! The actual target's interior holes lie strictly beyond the first clear's whole-board budget. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS SegmentRecipe

/-- Every actual non-frame target hole is farther from each side than the entire interior-hole count. -/
theorem target_interior_side_margins (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ targetHoles l p target \ Boundary.frame) :
    (targetHoles l p target \ Boundary.frame).card < q.1.val ∧
      q.1.val + (targetHoles l p target \ Boundary.frame).card < p.W := by
  have hcount := l.encodedSegments_interior_card_le p hl ha (l.canonical target)
  have houter := p.outer_distance
  obtain ⟨hhole, hframe⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hhole
  rcases List.mem_append.mp hs with hs | hs
  · have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) :=
      (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hcontains⟩
    obtain ⟨hx, hx'⟩ := l.fixedSegments_interior_column_margins p hl ha hfixed hframe
    change (targetHoles l p target \ Boundary.frame).card ≤ 2 * p.b p.levels at hcount
    omega
  · have hsignal : (q.1.val, q.2.val) ∈ pointHoles (l.signalSegments p (l.canonical target)) :=
      (mem_pointHoles _ _).mpr ⟨s, hs, hcontains⟩
    obtain ⟨i, hi, hnear⟩ := l.signalSegments_near_axis p hl (l.canonical target) hsignal
    have hi' : i < p.axes := hi.trans_le ha
    have hleft := Nat.mul_le_mul_right p.D (show 1 ≤ i + 1 by omega)
    have hright := Nat.mul_le_mul_right p.D (show i + 2 ≤ p.axes + 1 by omega)
    simp only [Nat.one_mul] at hleft
    have hx : p.D ≤ p.x i := hleft
    have hx' : p.x i + p.D ≤ p.W := by
      simpa only [Scales.Parameters.x, Scales.Parameters.W, Nat.add_mul, Nat.one_mul, two_mul, Nat.add_assoc] using hright
    simp only [Nat.dist_eq_max_sub_min] at hnear
    change (targetHoles l p target \ Boundary.frame).card ≤ 2 * p.b p.levels at hcount
    omega

/-- The actual first side-band clear encounters no target hole after the frame has been read. -/
theorem target_side_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    ((emit (frameSchedule p.W p.H) (targetHoles l p target)).remaining.filter fun q =>
      Direction.north.lane q ∈ sideBands p (targetHoles l p target \ Boundary.frame).card) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hband⟩ := Finset.mem_filter.mp hq
  rw [frame_remaining] at hq
  obtain ⟨hx, hx'⟩ := target_interior_side_margins l p hl ha target hq
  rw [sideBands] at hband
  have hb := (Finset.mem_filter.mp hband).2
  change (1 ≤ q.1.val ∧ q.1.val ≤ (targetHoles l p target \ Boundary.frame).card) ∨
    (p.W - (targetHoles l p target \ Boundary.frame).card ≤ q.1.val ∧ q.1.val < p.W) at hb
  omega

end PushPuzzle.Push.AcceptanceProgram

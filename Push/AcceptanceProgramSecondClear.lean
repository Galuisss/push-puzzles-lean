/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramFirstClear
public import Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed

/-! The actual main-axis prefixes pay for every hole outside the second clear's retained rows. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout SegmentRecipe

/-- Eight actual preparation blocks, through both main-axis prefix reads. -/
def mainAxisSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  firstRowSchedule l p k ++ [mainRound l p .upper, mainRound l p .lower]

/-- Every remaining real target hole lies on a row explicitly retained by the first clear. -/
theorem target_second_rows_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : q.2.val ∈ secondRowKeep l p := by
  have hqframe : q ∈ targetHoles l p target \ Boundary.frame := by
    rw [mainAxisSchedule, emit_remaining_append] at hq
    have hq := emit_remaining_subset _ _ hq
    rw [firstRowSchedule, emit_remaining_append] at hq
    have hq := emit_remaining_subset _ _ hq
    rw [firstTrimSchedule, emit_remaining_append] at hq
    have hh := emit_remaining_subset _ _ hq
    rwa [frame_remaining] at hh
  have hu : trimRound l p .upper ∈ mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [mainAxisSchedule, firstRowSchedule, firstTrimSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hd : trimRound l p .lower ∈ mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [mainAxisSchedule, firstRowSchedule, firstTrimSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hnotUpper := emit_stage_excluded hu hq
  have hnotLower := emit_stage_excluded hd hq
  have hMainU : mainRound l p .upper ∈ mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [mainAxisSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inl trivial)
  have hMainD : mainRound l p .lower ∈ mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [mainAxisSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    exact Or.inr (Or.inr trivial)
  have hnotMainU := emit_stage_excluded hMainU hq
  have hnotMainD := emit_stage_excluded hMainD hq
  obtain ⟨hqTarget, hframe⟩ := Finset.mem_sdiff.mp hqframe
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hqTarget
  rcases List.mem_append.mp hs with hs | hs
  · by_cases hn : s.start = s.finish
    · exact l.acceptanceFixedPointNarrowRow p hl hM hs hn hc hframe
    · have hcover := l.acceptanceFixedNonpointNarrowCover p hl hM hs hn hc hframe
      rcases hcover with hrow | hu | hd
      · exact hrow
      · exact False.elim (hnotUpper hu)
      · exact False.elim (hnotLower hd)
  · have hh := l.acceptanceSignalNarrowCover p hl hM (l.canonical target)
      ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
    rcases hh with hrow | hu | hd
    · exact hrow
    · exact False.elim (hnotMainU hu)
    · exact False.elim (hnotMainD hd)

/-- The second actual row clear has zero target loss. -/
private theorem target_second_row_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool) :
    ((emit (mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining.filter fun q => Direction.west.lane q ∈
        Finset.range (p.H + 1) \ secondRowKeep l p) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hline⟩ := Finset.mem_filter.mp hq
  exact (Finset.mem_sdiff.mp hline).2 (target_second_rows_supported l p hl hM target hq)

/-- The first nine literal preparation blocks. -/
def secondRowSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  mainAxisSchedule l p k ++ [.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)]

theorem preparation_take_nine (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    (preparation l p k).take 9 = secondRowSchedule l p k := by
  simp only [preparation, frameSchedule, secondRowSchedule, mainAxisSchedule, firstRowSchedule,
    firstTrimSchedule, firstRowKeep, secondRowKeep, mainRound, mainTop, mainBottom,
    List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
    reduceCtorEq, ite_true, ite_false]

/-- Every clear in the literal first nine target blocks deletes zero holes. -/
theorem secondRows_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) :
    (emit (secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [secondRowSchedule, emit_discarded_append]
  have hmain : (emit (mainAxisSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
    rw [mainAxisSchedule, emit_discarded_append, firstRows_discarded_zero l p hl hM ha target]
    simp only [mainRound, emit, Nat.add_zero]
  rw [hmain, Nat.zero_add]
  simp only [emit, Nat.add_zero]
  rw [target_second_row_clear_empty l p hl hM target, Finset.card_empty]

end PushPuzzle.Push.AcceptanceProgram

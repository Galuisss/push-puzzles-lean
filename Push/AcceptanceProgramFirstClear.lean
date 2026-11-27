/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramFixedRows
public import Push.AcceptanceProgram
import all Push.AcceptanceProgramLayout

/-! The actual first post-trim row clear removes no canonical target hole. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout SegmentRecipe

/-- The five actual preparation blocks before its first row clear. -/
def firstTrimSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  frameSchedule p.W p.H ++ [.clear .north (sideBands p k), trimRound l p .lower, trimRound l p .upper]

/-- Every remaining real target hole lies on a row explicitly retained by the first clear. -/
private theorem target_first_rows_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (firstTrimSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : q.2.val ∈ firstRowKeep l p := by
  have hqframe : q ∈ targetHoles l p target \ Boundary.frame := by
    rw [firstTrimSchedule, emit_remaining_append] at hq
    have hh := emit_remaining_subset _ _ hq
    rwa [frame_remaining] at hh
  have hu : trimRound l p .upper ∈ firstTrimSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [firstTrimSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hd : trimRound l p .lower ∈ firstTrimSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp only [firstTrimSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
    tauto
  have hnotUpper := emit_stage_excluded hu hq
  have hnotLower := emit_stage_excluded hd hq
  obtain ⟨hqTarget, hframe⟩ := Finset.mem_sdiff.mp hqframe
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hqTarget
  rcases List.mem_append.mp hs with hs | hs
  · by_cases hn : s.start = s.finish
    · exact l.acceptanceFixedPointRow p hl hM hs hn hc hframe
    · have hcover := l.acceptanceFixedNonpointCover p hl hM hs hn hc hframe
      rcases hcover with hrow | hu | hd
      · exact Finset.mem_union_left _ hrow
      · exact False.elim (hnotUpper hu)
      · exact False.elim (hnotLower hd)
  · exact signal_rows_keep l p hl hM (l.canonical target)
      ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)

/-- The literal first row clear deletes zero holes of the actual canonical target. -/
private theorem target_first_row_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool) :
    ((emit (firstTrimSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining.filter fun q => Direction.west.lane q ∈
        Finset.range (p.H + 1) \ firstRowKeep l p) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hline⟩ := Finset.mem_filter.mp hq
  exact (Finset.mem_sdiff.mp hline).2 (target_first_rows_supported l p hl hM target hq)

/-- The first six actual blocks, including the first post-trim row clear. -/
def firstRowSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  firstTrimSchedule l p k ++ [.clear .west (Finset.range (p.H + 1) \ firstRowKeep l p)]

/-- The complete initial trims and side-band clear preserve every target hole not paid by reads. -/
private theorem firstTrim_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (firstTrimSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [firstTrimSchedule, emit_discarded_append]
  have hframe : (emit (frameSchedule p.W p.H) (targetHoles l p target)).discarded = 0 := rfl
  rw [hframe, Nat.zero_add]
  simp only [emit, trimRound, Nat.add_zero]
  rw [target_side_clear_empty l p hl ha target, Finset.card_empty]

/-- Every clear in the literal first six-block target prefix deletes zero holes. -/
theorem firstRows_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) :
    (emit (firstRowSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [firstRowSchedule, emit_discarded_append, firstTrim_discarded_zero l p hl ha target, Nat.zero_add]
  simp only [emit, Nat.add_zero]
  rw [target_first_row_clear_empty l p hl hM target, Finset.card_empty]

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgram
import all PushS.PortStreetSupport
import all PushS.PortSegments

/-! The second real endpoint support follows from whole-line reads and the actual non-street column clear. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem frame_second (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hf : q ∈ Boundary.frame) : q ∈ (supportCoordinates l p).second := by
  apply (second_support_iff l p q).mpr
  rcases frame_onStreet l p hf with hx | hy
  · exact Or.inl (Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hx)))
  · exact Or.inr (List.mem_toFinset.mpr hy)

/-- Every accepted endpoint, after filling the new markers, lies on F(X∪G∪S,Y). -/
theorem program_second_supported (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Support.Supported (supportCoordinates l p).second (Blocked.fill t (newCentralMarkers l p)) := by
  intro q hq
  have hholes : q ∈ PushS.holes t := (PushS.mem_holes _).mpr (fun hb => hq (Finset.mem_union_left _ hb))
  have hnew : q ∉ newCentralMarkers l p := fun hm => hq (Finset.mem_union_right _ hm)
  by_contra hout
  have hframe : q ∉ Boundary.frame := fun hf => hout (frame_second l p hf)
  have hrows : q.2.val ∉ newMarkerRows p := by
    intro hy
    exact hnew (program_new_rows_stock l p hl hM haxes initial target hr hp hs ha hholes hframe hy)
  have hprefix : ∃ rest, schedule l p (targetHoles l p target \ Boundary.frame).card =
      workReadSchedule l p (targetHoles l p target \ Boundary.frame).card ++
        .clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p)) :: rest := by
    unfold schedule workReadSchedule thirdRowSchedule axisSchedule axisTail workTail preparation
    simp only [axisReadRound, thirdRowKeep, List.append_assoc, List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨rest, hprefix⟩ := hprefix
  have hclean := (program_clean_execution l p hl hM haxes initial target hr hs ha).2
  unfold program at hclean
  rw [hprefix, emit_rounds_append, instructions, List.flatMap_append] at hclean
  obtain ⟨F, hF, hbefore, hafter⟩ := clean_append _ _ (PushS.holes t) hclean
  have hF' : Scan.eval (instructions (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).rounds) (PushS.holes t) = some F := hF
  have hqF := clean_unread_survives _ _ _ F hbefore hF' hholes (by
    intro stage hstage ht
    rcases early_read_lane_cover l p hl hM haxes _ hstage ht with hf | hsupport | hrow
    · exact hframe hf
    · exact hout hsupport
    · exact hrows hrow)
  obtain ⟨G, _, hkeep, _⟩ := hafter
  have hnot := hkeep q hqF
  change q.1.val ∉ Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p) at hnot
  have hcols : q.1.val ∈ auxiliaries l p ∪ cores l p := by
    by_contra hbad
    exact hnot (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.1.isLt, hbad⟩)
  apply hout
  apply (second_support_iff l p q).mpr ∘ Or.inl
  rcases Finset.mem_union.mp hcols with haux | hcore
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_sdiff.mp haux).1)
  · obtain ⟨i, hi, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp (l.acceptanceCore_subset_axes p hl hcore))
    have hx := heq ▸ axis_in_streetColumns l p (List.mem_range.mp hi)
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hx))

end PushPuzzle.Push.AcceptanceSoundness

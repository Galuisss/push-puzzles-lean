/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportResidual
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentralFlanks
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceSoundnessCentralSamples
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramThirdClear
import all PushS.PortSegments

/-! The actual residuals retain the two flank and short-train sample barriers until their own row reads. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProgram

/-- Every actual sample column has the literal D+4 sample marker added by the emitter. -/
theorem actual_sample_marker (l : PortLayout) (p : Scales.Parameters) (x : Fin (p.W + 1))
    (hx : x.val ∈ samples l p) :
    ∃ g : Cell (p.W + 1) (p.H + 1), g.1 = x ∧ g.2.val = p.D + 4 ∧ g ∈ newCentralMarkers l p := by
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨p.D + 4, by omega⟩)
  have hx0 : x.val ≠ 0 := by omega
  have hxW : x.val ≠ p.W := by
    intro he
    have haxis : p.x p.axes = p.W := rfl
    rcases hx with hx | hx
    · exact sample_off_axis p i p.axes (by omega) (hx.symm.trans (he.trans haxis.symm))
    · exact sample_off_axis p i p.axes (by omega) (hx.symm.trans (he.trans haxis.symm))
  have hfixed : point x.val (p.D + 4) ∈ l.fixedSegments p := by
    unfold fixedSegments markedInterior
    apply List.mem_append_right
    apply List.mem_append_right
    apply List.mem_flatMap.mpr
    refine ⟨i, hi, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    rcases hx with hx | hx
    · exact Or.inl (congrArg (fun x => point x (p.D + 4)) hx)
    · exact Or.inr (congrArg (fun x => point x (p.D + 4)) hx)
  refine ⟨g, rfl, rfl, Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨?_, ?_⟩, ?_⟩, ?_⟩⟩
  · exact (SegmentRecipe.mem_holes _ g).mpr ⟨point x.val (p.D + 4), hfixed, by simp [point, PortLayout.segment, Segment.Contains, g]⟩
  · intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame g).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, g] at hd <;> omega
  · change p.D ≤ p.D + 4 + 4 ∧ p.D + 4 ≤ p.D + 4
    omega
  · change p.D + 4 ≠ p.D
    omega

section Source
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
  {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ} {s t : State (p.W + 1) (p.H + 1)}
  (hr : Reachable B cap s t) (hp : s.player ∈ Boundary.frame) (hs : PushS.holes s = targetHoles l p initial)
  (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))

include hl hM haxes initial hr hp hs ha

/-- Both actual flank markers remain in R10, immediately before their own saturated horizontal read. -/
theorem flank_markers_residual {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.centralMarkers p)
    (hy : g.2.val = p.D - 2 ∨ g.2.val = p.D + 2) :
    g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 10 := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      flankBefore l p target ++ readRows p .east {p.D - 2, p.D + 2} :: right := by
    unfold schedule preparation flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns,
      firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  obtain ⟨F, hF, hmarkers⟩ := central_stage_saturation_trace l p hl hM haxes initial target hr hp hs ha
    (flankBefore l p target) right .east {p.D - 2, p.D + 2} (Or.inr rfl) (by
      intro y hy
      have hD := p.outer_distance
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy
      omega) hsplit ⟨_, rfl⟩ (by intro q hq hrow; exact flank_target_kept l p hl hM haxes target hq hrow)
  have htake : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 10 = flankBefore l p target := by
    simp only [schedule, preparation, frameSchedule, flankBefore, sideClearSchedule,
      mainRound, mainTop, mainBottom, privateRound, privateColumns, firstRowKeep, secondRowKeep,
      reduceCtorEq, ite_true, ite_false, List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  unfold roundResidual
  rw [htake, hF]
  exact hmarkers (Finset.mem_filter.mpr ⟨hg, by simpa only [Finset.mem_insert, Finset.mem_singleton] using hy⟩)

/-- Every actual short-train sample marker remains in R22 before its own saturated D+4 row read. -/
theorem sample_markers_residual {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.centralMarkers p)
    (hy : g.2.val = p.D + 4) :
    g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 22 := by
  have hsplit : ∃ right, schedule l p (targetHoles l p target \ Boundary.frame).card =
      sampleBefore l p target ++ readRows p .east {p.D + 4} :: right := by
    unfold schedule preparation sampleBefore guardBefore flankBefore sideClearSchedule
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns, axisReadRound,
      thirdRowKeep, firstRowKeep, secondRowKeep, reduceCtorEq, ite_true, ite_false, List.append_assoc,
      List.cons_append, List.nil_append]
    exact ⟨_, rfl⟩
  obtain ⟨right, hsplit⟩ := hsplit
  obtain ⟨F, hF, hmarkers⟩ := central_stage_saturation_trace l p hl hM haxes initial target hr hp hs ha
    (sampleBefore l p target) right .east {p.D + 4} (Or.inr rfl) (by
      intro y hy
      have he := Finset.mem_singleton.mp hy
      omega) hsplit (by unfold sampleBefore guardBefore flankBefore; exact ⟨_, by simp only [List.append_assoc]; rfl⟩)
    (by intro q hq hrow; exact sample_target_kept l p hl hM haxes target hq (Finset.mem_singleton.mp hrow))
  have htake : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 22 = sampleBefore l p target := by
    simp only [schedule, preparation, frameSchedule, sampleBefore, guardBefore, flankBefore, sideClearSchedule,
      mainRound, mainTop, mainBottom, privateRound, privateColumns, firstRowKeep, secondRowKeep,
      thirdRowKeep, axisReadRound, reduceCtorEq, ite_true, ite_false, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero]
  unfold roundResidual
  rw [htake, hF]
  exact hmarkers (Finset.mem_filter.mpr ⟨hg, Finset.mem_singleton.mpr hy⟩)

end Source
end PushPuzzle.Push.AcceptanceSoundness

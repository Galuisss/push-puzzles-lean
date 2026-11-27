/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportInterlevel
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgram
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentralStock
import all PushS.PortLayoutCoordinates

/-! The second actual row clear leaves no available hole outside the lower half-depth front. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- Apart from the bottom frame, every retained second-clear row is at least half a first-level depth from the bottom. -/
private theorem secondRowKeep_lower_depth (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q.2.val ∈ secondRowKeep l p) (hbottom : q.2.val ≠ p.H) :
    p.Y 1 / 2 ≤ p.H - q.2.val := by
  have hD := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hD
  have hY := p.Y_ge 1
  have hH : p.H = 2 * p.D := rfl
  have hqH := q.2.isLt
  simp only [secondRowKeep, keepRows, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hq
  rcases hq with ((hw | hc) | hm) | ht
  · simp only [workRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (h0 | hH') | hw
    · omega
    · exact False.elim (hbottom hH')
    · obtain ⟨v, hv, hy⟩ := List.mem_flatMap.mp hw
      have hb := working_depth_bounds l p hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy <;> omega
  · simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (hc | hc) | hc
    · omega
    · omega
    · obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hc
      have hkm := List.mem_range.mp hk
      have hb := interlevelDepth_bounds p (j := k + 1) (by omega) (by omega)
      have hlo := PortLayout.Y_le p (show 1 ≤ k + 1 by omega)
      simp only [interlevelDepth] at hb
      simp only [show k + 1 + 1 = k + 2 by omega] at hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with hy | hy <;> omega
  · rcases hm with hm | hm | hm | hm <;> omega
  · omega

/-- Every actual residual after the frame and side clear is disjoint from the original frame. -/
theorem canonical_residual_not_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (n : ℕ) (hn : 3 ≤ n) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) n) : q ∉ Boundary.frame := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hq3 := roundResidual_antitone stages T E hc hn hq
  have htake3 : stages.take 3 = sideClearSchedule l p target := by
    simp only [stages, schedule, preparation, frameSchedule, sideClearSchedule, T,
      List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  unfold roundResidual at hq3
  rw [htake3, program_sideClear_eval l p target ha, Option.getD_some,
    program_sideClear_remaining l p hl hM haxes initial target hr
      (canonical_initial_holes l p hl hM haxes initial target) ha] at hq3
  exact (Finset.mem_sdiff.mp hq3).2

/-- The actual private-read input obeys the immediately preceding zero-loss row clear. -/
theorem canonical_private_input_rows (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 9) : q.2.val ∈ secondRowKeep l p := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[8]? = some (.clear .west (Finset.range (p.H + 1) \ secondRowKeep l p)) := by
    simp only [stages, schedule, preparation, frameSchedule, secondRowKeep, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hq8 := roundResidual_antitone stages T E hc (by omega : 8 ≤ 9) hq
  have hkeep := (roundResidual_clear_keeps stages T E 8 hc hi hq8).2
  by_contra hn
  exact hkeep (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.2.isLt, hn⟩)

/-- Every actual hole entering the private-column read is at or beyond the lower half-depth row. -/
theorem canonical_private_input_depth (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 9) : p.Y 1 / 2 ≤ p.H - q.2.val := by
  apply secondRowKeep_lower_depth l p (canonical_private_input_rows l p hl hM haxes initial target hr ha hq)
  intro hb
  apply canonical_residual_not_frame l p hl hM haxes initial target hr ha 9 (by omega) hq
  exact (Boundary.mem_frame q).mpr ⟨.south, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hb]⟩

end PushPuzzle.Push.AcceptanceSoundness

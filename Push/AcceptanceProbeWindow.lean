/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramThirdClear
public import Push.AcceptanceProgramInterlevelStock
public import PushS.PortDepthBands
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramTrimStock
import all PushS.PortLayoutCoordinates
import all PushS.PortSegments

/-! The third row clear retains only the two own-level upper working rows before the next marker. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem cut_not_window (p : Scales.Parameters) {j y : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (lower : p.Y j ≤ y) (upper : y < trimDepth p j) : y ∉ cutRows p := by
  have hi := trimDepth_lt_D p hj hjm
  have Y1 := readDepth_add_lt_D p 1
  rw [readDepth_eq p (by omega) p.levels_pos] at Y1
  have H : p.H = 2 * p.D := rfl
  intro hy
  simp only [cutRows, List.mem_toFinset, List.mem_append] at hy
  rcases hy with base | level
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at base
    omega
  · obtain ⟨k, hk, hrow⟩ := List.mem_flatMap.mp level
    have hk := List.mem_range.mp hk
    have bounds := interlevelDepth_bounds p (j := k + 1) (by omega) (by omega)
    simp only [interlevelDepth, Nat.add_assoc, Nat.reduceAdd] at bounds
    have margins := readDepth_add_lt_D p (k + 2)
    rw [readDepth_eq p (by omega) (by omega)] at margins
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hrow
    rcases hrow with hrow | hrow
    · by_cases before : k + 1 < j
      · have le := Y_le p (show k + 2 ≤ j by omega)
        omega
      · have jm : j < p.levels := by omega
        have first := Y_le p (show j ≤ k + 1 by omega)
        have next := Y_le p (show j + 1 ≤ k + 2 by omega)
        rw [trimDepth, ite_eq_left jm] at upper
        omega
    · omega

/-- Between an upper work depth and its first marker, the actual third clear retains only its two working rows. -/
theorem upper_third_window (l : PortLayout) (p : Scales.Parameters) {j y : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) (keep : y ∈ thirdRowKeep l p)
    (lower : p.Y j ≤ y) (upper : y < trimDepth p j) : y = p.Y j ∨ y = p.Y j + 2 := by
  have hi := trimDepth_lt_D p hj hjm
  have H : p.H = 2 * p.D := rfl
  have positive := p.Y_ge j
  simp only [thirdRowKeep, Finset.mem_union, Finset.mem_singleton] at keep
  rcases keep with (work | cut) | central
  · simp only [workRows, List.mem_toFinset, List.mem_append] at work
    rcases work with base | working
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at base
      omega
    · obtain ⟨v, hv, row⟩ := List.mem_flatMap.mp working
      have margin := workingRows_le_last l p hv
      have gap := last_depth_margin p
      simp only [List.mem_cons, List.not_mem_nil, or_false] at row
      rcases row with row | row
      · have bands := l.workingDepthCoordinates_bands p hj hjm hv
        rw [readDepth_eq p hj hjm] at bands
        rcases bands with shallow | own | ⟨jm, deep⟩
        · left; omega
        · right; omega
        · rw [readDepth_eq p (by omega) (by omega)] at deep
          rw [trimDepth, ite_eq_left jm] at upper
          omega
      · omega
  · exact (cut_not_window p hj hjm lower upper cut).elim
  · omega

end PushPuzzle.Push.AcceptanceProgram

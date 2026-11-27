/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramHalfStockGeometry
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramInterlevelStock
import all PushS.PortSegments
import all PushS.PortStreetSeparation
import all PushS.PortWalkBudget
import all PushS.PortLayoutCoordinates

/-! The actual first private-read window has only its four owned depths and the lower central exception. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem firstTrim_le (p : Scales.Parameters) : trimDepth p 1 ≤ p.D - 2 := by
  by_cases hm : 1 < p.levels
  · have hb := interlevelDepth_bounds p le_rfl hm
    simp only [trimDepth, ite_eq_left hm]
    change interlevelDepth p 1 ≤ p.D - 2
    omega
  · simp only [trimDepth, ite_eq_right hm, le_refl]

private theorem short_work_depth (l : PortLayout) (p : Scales.Parameters)
    (hcenters : l.gateCenterCoordinates ≠ []) {v : ℕ}
    (hv : v ∈ l.workingDepthCoordinates p) (hshort : v < trimDepth p 1) :
    v = p.Y 1 ∨ v = p.Y 1 + 2 := by
  change v ∈ workingRows l (coordinates p) at hv
  obtain ⟨k, hk, hv⟩ := List.mem_flatMap.mp hv
  have hk := List.mem_range.mp hk
  change k < p.levels at hk
  have hn : (centers l).isEmpty = false := List.isEmpty_eq_false_iff.mpr hcenters
  change v ∈ (if (centers l).isEmpty then
    [readDepth p (k + 1) - 2, readDepth p (k + 1), readDepth p (k + 1) + 2]
    else [readDepth p (k + 1), readDepth p (k + 1) + 2]) at hv
  rw [hn, ite_eq_right (by decide), readDepth_eq p (by omega) (by omega)] at hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  by_cases he : k + 1 = 1
  · simpa only [he] using hv
  · have hm : 1 < p.levels := by omega
    have hb := interlevelDepth_bounds p le_rfl hm
    simp only [Nat.reduceAdd] at hb
    have hle := Y_le p (show 2 ≤ k + 1 by omega)
    rw [trimDepth, ite_eq_left hm] at hshort
    change v < interlevelDepth p 1 at hshort
    omega

private theorem work_window (l : PortLayout) (p : Scales.Parameters)
    (hcenters : l.gateCenterCoordinates ≠ []) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q.2.val ∈ workRows l p) (hbottom : q.2.val ≠ p.H)
    (hshort : p.H - q.2.val < trimDepth p 1) :
    p.H - q.2.val = p.Y 1 ∨ p.H - q.2.val = p.Y 1 + 2 := by
  have htrim := firstTrim_le p
  have hh : p.H = 2 * p.D := rfl
  simp only [workRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (h0 | hH) | hq
  · omega
  · exact False.elim (hbottom hH)
  · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp hq
    have hb := working_depth_bounds l p hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he
    · omega
    · have he' : p.H - q.2.val = v := by omega
      rw [he']
      exact short_work_depth l p hcenters hv (he' ▸ hshort)

private theorem cut_window (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q.2.val ∈ cutRows p) (hshort : p.H - q.2.val < trimDepth p 1) :
    p.H - q.2.val = p.Y 1 / 2 := by
  have htrim := firstTrim_le p
  have hh : p.H = 2 * p.D := rfl
  have hy := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hy
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with (hc | hhalf) | hq
  · omega
  · omega
  · obtain ⟨k, hk, he⟩ := List.mem_flatMap.mp hq
    have hk := List.mem_range.mp hk
    have hm : 1 < p.levels := by omega
    have hb := interlevelDepth_bounds p (show 1 ≤ k + 1 by omega) (show k + 1 < p.levels by omega)
    have hy0 := Y_le p (show 1 ≤ k + 1 by omega)
    have hy1 := Y_le p (show 2 ≤ k + 2 by omega)
    rw [trimDepth, ite_eq_left hm] at hshort
    unfold interlevelDepth at hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, Nat.add_assoc, Nat.reduceAdd] at he hb hshort
    omega

/-- Below the first trim boundary, the retained rows are exactly the four possible private depths,
with the actual lower central `D+4` row as the remaining one-level exception. -/
private theorem privateWindow_rows (l : PortLayout) (p : Scales.Parameters)
    (hcenters : l.gateCenterCoordinates ≠ []) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q.2.val ∈ secondRowKeep l p) (hbottom : q.2.val ≠ p.H)
    (hshort : pageDepth p .lower q < trimDepth p 1) :
    pageDepth p .lower q ∈ ({p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2} : Finset ℕ) ∨
      q.2.val = p.D + 4 := by
  change p.H - q.2.val < trimDepth p 1 at hshort
  change p.H - q.2.val ∈ ({p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2} : Finset ℕ) ∨ _
  simp only [secondRowKeep, keepRows, Finset.mem_union] at hq
  rcases hq with ((hw | hc) | hf) | ht
  · have hr := work_window l p hcenters hw hbottom hshort
    left
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rcases hr with hr | hr
    · exact Or.inr (Or.inl hr)
    · exact Or.inr (Or.inr (Or.inr hr))
  · have hr := cut_window p hc hshort
    exact Or.inl (Finset.mem_insert.mpr (Or.inl hr))
  · have ht := firstTrim_le p
    have hh : p.H = 2 * p.D := rfl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hf
    right
    omega
  · have ht := Finset.mem_singleton.mp ht
    have hD := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hD
    have hh : p.H = 2 * p.D := rfl
    left
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega

/-- A real private column supplies the gate witness needed by the exact private-window classification. -/
theorem privateColumn_window (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p)
    (hq : q.2.val ∈ secondRowKeep l p) (hbottom : q.2.val ≠ p.H)
    (hshort : pageDepth p .lower q < trimDepth p 1) :
    pageDepth p .lower q ∈ ({p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2} : Finset ℕ) ∨
      q.2.val = p.D + 4 := by
  obtain ⟨i, hi, _⟩ := privateColumn_gate l p hx
  exact privateWindow_rows l p (fun he => List.not_mem_nil (he ▸ hi)) hq hbottom hshort

end PushPuzzle.Push.AcceptanceProgram

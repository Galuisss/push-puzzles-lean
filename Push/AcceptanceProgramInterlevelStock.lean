/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWorkClear
public import PushS.PortEndpointTail
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramWorkClear
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates
import all PushS.PortStreetSeparation

/-! Exact page and level ownership of the actual interlevel acceptance rows. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The literal midpoint used by each nondeepest level's marker check. -/
@[expose] def interlevelDepth (p : Scales.Parameters) (j : ℕ) : ℕ :=
  (p.Y j + p.Y (j + 1)) / 2

/-- The actual upper or reflected lower row read by the corresponding marker check. -/
@[expose] def interlevelRow (p : Scales.Parameters) (side : Side) (j : ℕ) : ℕ :=
  if side = .upper then interlevelDepth p j else p.H - interlevelDepth p j

/-- Every check midpoint lies strictly between the adjacent work bands and before the central band. -/
theorem interlevelDepth_bounds (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels) :
    p.Y j + 2 < interlevelDepth p j ∧ interlevelDepth p j + 2 < p.Y (j + 1) ∧
      interlevelDepth p j + 64 < p.D := by
  have hg := p.interlevel_margin j hj
  have hd := readDepth_add_lt_D p (j + 1)
  rw [readDepth_eq p (by omega) (by omega)] at hd
  unfold interlevelDepth
  omega

private theorem interlevelDepth_strictMono (p : Scales.Parameters) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hjm : j < p.levels) : interlevelDepth p i < interlevelDepth p j := by
  have hi' := interlevelDepth_bounds p hi (show i < p.levels by omega)
  have hj' := interlevelDepth_bounds p (show 1 ≤ j by omega) hjm
  have hm := Y_le p (show i + 1 ≤ j by omega)
  omega

private theorem interlevelDepth_injective (p : Scales.Parameters) {i j : ℕ}
    (hi : 1 ≤ i) (him : i < p.levels) (hj : 1 ≤ j) (hjm : j < p.levels)
    (he : interlevelDepth p i = interlevelDepth p j) : i = j := by
  rcases lt_trichotomy i j with h | h | h
  · have := interlevelDepth_strictMono p hi h hjm
    omega
  · exact h
  · have := interlevelDepth_strictMono p hj h him
    omega

/-- A literal marker-check row identifies both its page and its allocated level uniquely. -/
theorem interlevelRow_eq_iff (p : Scales.Parameters) (first second : Side) {i j : ℕ}
    (hi : 1 ≤ i) (him : i < p.levels) (hj : 1 ≤ j) (hjm : j < p.levels) :
    interlevelRow p first i = interlevelRow p second j ↔ first = second ∧ i = j := by
  constructor
  · intro he
    have hb := interlevelDepth_bounds p hi him
    have hc := interlevelDepth_bounds p hj hjm
    have hh : p.H = 2 * p.D := rfl
    cases first <;> cases second <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at he
    · exact ⟨rfl, interlevelDepth_injective p hi him hj hjm he⟩
    · omega
    · omega
    · exact ⟨rfl, interlevelDepth_injective p hi him hj hjm (by omega)⟩
  · rintro ⟨rfl, rfl⟩
    rfl

/-- A marker-check row meets neither the shared cut nor the lower half-depth row. -/
theorem interlevelRow_ne_cut_half (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    interlevelRow p side j ≠ p.D ∧ interlevelRow p side j ≠ p.H - p.Y 1 / 2 := by
  have hb := interlevelDepth_bounds p hj hjm
  have hy := Y_le p hj
  have hd := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hd
  have hh : p.H = 2 * p.D := rfl
  cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] <;> omega

private theorem working_depth_bounds (l : PortLayout) (p : Scales.Parameters) {v : ℕ}
    (hv : v ∈ l.workingDepthCoordinates p) : p.Y 1 - 2 ≤ v ∧ v + 62 < p.D := by
  change v ∈ workingRows l (coordinates p) at hv
  obtain ⟨k, hk, hv⟩ := List.mem_flatMap.mp hv
  have hk := List.mem_range.mp hk
  change k < p.levels at hk
  have hlo := Y_le p (show 1 ≤ k + 1 by omega)
  have hd := readDepth_add_lt_D p (k + 1)
  rw [readDepth_eq p (by omega) (by omega)] at hd
  change v ∈ (if (centers l).isEmpty then
    [readDepth p (k + 1) - 2, readDepth p (k + 1), readDepth p (k + 1) + 2]
    else [readDepth p (k + 1), readDepth p (k + 1) + 2]) at hv
  rw [readDepth_eq p (by omega) (by omega)] at hv
  split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega

private theorem interlevelDepth_not_working (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) : interlevelDepth p j ∉ l.workingDepthCoordinates p := by
  intro hw
  have hg := l.workingDepthCoordinates_interlevel_gap p hj hjm hw
  rw [readDepth_eq p hj (by omega), readDepth_eq p (by omega) (by omega)] at hg
  have hb := interlevelDepth_bounds p hj hjm
  omega

/-- No literal interlevel check row is a selected work row on either page. -/
theorem interlevelRow_not_work (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) : interlevelRow p side j ∉ workRows l p := by
  intro hw
  have hb := interlevelDepth_bounds p hj hjm
  have hh : p.H = 2 * p.D := rfl
  simp only [workRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with (h0 | hH) | hw
  · cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at h0 <;> omega
  · cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at hH <;> omega
  · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp hw
    have hvb := working_depth_bounds l p hv
    have hn := interlevelDepth_not_working l p hj hjm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at he <;>
      rcases he with he | he
    · exact hn (he ▸ hv)
    · omega
    · omega
    · have he' : v = interlevelDepth p j := by omega
      exact hn (he' ▸ hv)

/-- Every actual acceptance-cut row is separate from every selected working row. -/
theorem cutRows_disjoint_workRows (l : PortLayout) (p : Scales.Parameters) :
    Disjoint (cutRows p) (workRows l p) := by
  apply Finset.disjoint_left.mpr
  intro row hc hw
  simp only [cutRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with (hc | hc) | hc
  · have hh : p.H = 2 * p.D := rfl
    simp only [workRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (h0 | hH) | hw
    · have hd := readDepth_add_lt_D p 1
      omega
    · have hd := readDepth_add_lt_D p 1
      omega
    · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp hw
      have hb := working_depth_bounds l p hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      omega
  · have hh : p.H = 2 * p.D := rfl
    have hy := p.Y_ge 1
    have hd := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hd
    simp only [workRows, List.mem_toFinset, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with (h0 | hH) | hw
    · omega
    · omega
    · obtain ⟨v, hv, he⟩ := List.mem_flatMap.mp hw
      have hb := working_depth_bounds l p hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      omega
  · obtain ⟨k, hk, he⟩ := List.mem_flatMap.mp hc
    have hk := List.mem_range.mp hk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with he | he
    · exact interlevelRow_not_work l p .upper (by omega) (by omega) (he ▸ hw)
    · exact interlevelRow_not_work l p .lower (by omega) (by omega) (he ▸ hw)

/-- The lower half-depth check row is separate from every actual working row. -/
theorem halfRow_not_workRows (l : PortLayout) (p : Scales.Parameters) :
    p.H - p.Y 1 / 2 ∉ workRows l p := by
  apply Finset.disjoint_left.mp (cutRows_disjoint_workRows l p)
  apply List.mem_toFinset.mpr
  apply List.mem_append_left
  exact List.mem_cons_of_mem _ (List.mem_cons_self ..)

private theorem marker_row (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : pageDepth p side q = trimDepth p j) : q.2.val = interlevelRow p side j := by
  have hb := interlevelDepth_bounds p hj hjm
  have hh : p.H = 2 * p.D := rfl
  have hq := q.2.isLt
  cases side <;> simp only [pageDepth, interlevelRow, trimDepth, ite_eq_left hjm,
    interlevelDepth, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega

/-- On a given marker row the actual post-work stock has precisely that page and level's metadata. -/
private theorem workStock_interlevelRow (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hs : WorkStock l p q) (hy : q.2.val = interlevelRow p side j) :
    ∃ a ∈ pageColumns l p side, a.level = j ∧ q.1.val = a.column ∧
      pageDepth p side q = trimDepth p j := by
  cases hs with
  | interlevel other hm =>
    obtain ⟨a, ha, hlow, hhigh, hx, hd⟩ := hm
    have hr := marker_row p other hlow hhigh hd
    obtain ⟨he, hj'⟩ := (interlevelRow_eq_iff p other side hlow hhigh hj hjm).mp (hr.symm.trans hy)
    subst other
    exact ⟨a, ha, hj', hx, hj' ▸ hd⟩
  | half hh _ => exact False.elim ((interlevelRow_ne_cut_half p side hj hjm).2 (hy.symm.trans hh))
  | cut hc _ => exact False.elim ((interlevelRow_ne_cut_half p side hj hjm).1 (hy.symm.trans hc))

/-- Every remaining canonical reference hole on a marker-check row belongs to that same actual page and level.
The preceding marker checks may be any literal prefix; only the real twenty-five-block work prefix is needed. -/
theorem interlevel_target_residual_metadata (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (before : List Template) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit before ((emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining)).remaining)
    (hy : q.2.val = interlevelRow p side j) :
    ∃ a ∈ pageColumns l p side, a.level = j ∧ q.1.val = a.column ∧
      pageDepth p side q = trimDepth p j := by
  have hq := emit_remaining_subset _ _ hq
  rw [workSchedule, emit_remaining_append] at hq
  have hw := emit_remaining_subset _ _ hq
  exact workStock_interlevelRow l p side hj hjm (workRead_inventory l p hl hM ha target hw) hy

end PushPuzzle.Push.AcceptanceProgram

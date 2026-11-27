/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportLowerLevels
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortLayoutCoordinates

/-! Every real lower marker-row payment comes from its own physical page and level. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem pageColumn_public_or_first (l : PortLayout) (p : Scales.Parameters)
    (side : Side) {a : PageColumn} (ha : a ∈ AcceptanceProgram.pageColumns l p side) :
    a.privateColumn = false ∨ a.level = 1 := by
  unfold AcceptanceProgram.pageColumns at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨e, _, ha⟩ := List.mem_flatMap.mp ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> exact Or.inl rfl
  · split at ha
    next h =>
      obtain ⟨i, _, ha⟩ := List.mem_flatMap.mp ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> exact Or.inr rfl
    next h => cases ha

/-- At its actual lower marker-row read, every real remaining hole belongs to that exact lower metadata level. -/
theorem canonical_lower_marker_input_metadata (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ pageResidual l p target (PushS.holes t) (2 * j + 1))
    (hy : q.2.val = interlevelRow p .lower j) :
    ∃ a ∈ AcceptanceProgram.pageColumns l p .lower, a.level = j ∧ q.1.val = a.column := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hqglobal : q ∈ roundResidual stages T E (25 + (2 * j + 1)) := by
    rw [canonical_pageResidual_eq l p hl hM haxes initial target hr ha]
    exact hq
  have hq25 := roundResidual_antitone stages T E hc (show 25 ≤ 25 + (2 * j + 1) by omega) hqglobal
  have hcore := canonical_core_page_residual_empty l p hl hM haxes initial target hr ha (2 * j + 1) (by omega) hq
  have haux : q.1.val ∈ auxiliaries l p :=
    (Finset.mem_union.mp (canonical_page_residual_columns l p hl hM haxes initial target hr ha hq25)).resolve_right hcore
  have hb := interlevelDepth_bounds p hj hjm
  have hH : p.H = 2 * p.D := rfl
  have hrow := q.2.isLt
  have hdeep : p.D < q.2.val := by simp only [interlevelRow, reduceCtorEq, ite_false] at hy; omega
  have hlive : q.1.val ∈ lowerLiveColumns l p := by
    by_contra hn
    have h := canonical_nonlive_lower_depth_le_cut l p hl hM haxes initial target hr ha hq25 haux hn
    omega
  obtain ⟨a, hac, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp hlive)
  obtain ⟨hac, halevel⟩ := List.mem_filter.mp hac
  have halevel : 1 ≤ a.level ∧ a.level < p.levels := of_decide_eq_true halevel
  have hj_eq : a.level = j := by
    rcases lt_trichotomy a.level j with hlt | he | hgt
    · have h := canonical_lower_level_finished_empty l p hl hM haxes initial target hr ha hac
        halevel.1 halevel.2 (2 * j + 1) (by omega) hq hax.symm
      omega
    · exact he
    · have hpublic : a.privateColumn = false := by
        rcases pageColumn_public_or_first l p .lower hac with hp | hp
        · exact hp
        · omega
      have hbound := canonical_trim_retained_depth l p hl hM haxes initial target hr ha .lower hac hpublic
        (25 + (2 * j + 1)) (by simp only [reduceCtorEq, ite_false]; omega) hqglobal hax.symm
      have hmono := PortLayout.Y_le p (show j + 1 ≤ a.level by omega)
      simp only [pageDepth, interlevelRow, reduceCtorEq, ite_false, hy] at hbound
      simp only [interlevelRow, reduceCtorEq, ite_false] at hy
      omega
  exact ⟨a, hac, hj_eq, hax.symm⟩

end PushPuzzle.Push.AcceptanceSoundness

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportLowerRowStock
import all Push.AcceptanceSoundnessSupportLowerRowStock
import all Push.AcceptanceSoundnessSupportPagePositions
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram
import all PushS.PortLayoutCoordinates

/-! The actual upper marker-row reads have exactly their own page and level's candidate columns. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- After an upper level's real zero-loss clear, its columns carry no surviving page-check holes. -/
private theorem canonical_upper_level_finished_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {a : PageColumn} (hac : a ∈ AcceptanceProgram.pageColumns l p .upper)
    (hj : 1 ≤ a.level) (hjm : a.level < p.levels) (n : ℕ)
    (hn : (pageChecks l p .lower).length + 2 * a.level + 1 ≤ n)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ pageResidual l p target (PushS.holes t) n) :
    q.1.val ≠ a.column := by
  have hc := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hi := (pageCheck_upper_level_positions l p hj hjm).2
  have hqBefore := roundResidual_antitone _ _ _ hc
    (show (pageChecks l p .lower).length + 2 * a.level ≤ n by omega) hq
  have hkeep := (roundResidual_clear_keeps _ _ _ _ hc hi hqBefore).2
  intro hx
  apply hkeep
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨hac, by simp⟩, hx.symm⟩)

/-- At each actual upper marker-row read, all real candidates have that exact upper-page metadata level. -/
theorem canonical_upper_marker_input_metadata (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ pageResidual l p target (PushS.holes t) ((pageChecks l p .lower).length + (2 * j - 1)))
    (hy : q.2.val = interlevelRow p .upper j) :
    ∃ a ∈ AcceptanceProgram.pageColumns l p .upper, a.level = j ∧ q.1.val = a.column := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  let n := (pageChecks l p .lower).length + (2 * j - 1)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hcpage := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hqglobal : q ∈ roundResidual stages T E (25 + n) := by
    rw [canonical_pageResidual_eq l p hl hM haxes initial target hr ha]
    exact hq
  have hq25 := roundResidual_antitone stages T E hc (show 25 ≤ 25 + n by omega) hqglobal
  have hlen : 3 ≤ (pageChecks l p .lower).length := by rw [pageChecks_length]; simp
  have hcore := canonical_core_page_residual_empty l p hl hM haxes initial target hr ha n (by dsimp only [n]; omega) hq
  have haux : q.1.val ∈ auxiliaries l p :=
    (Finset.mem_union.mp (canonical_page_residual_columns l p hl hM haxes initial target hr ha hq25)).resolve_right hcore
  have hqHead := roundResidual_antitone _ _ _ hcpage
    (show (pageChecks l p .lower).length ≤ n by dsimp only [n]; omega) hq
  have hkeep := (roundResidual_clear_keeps _ _ _ _ hcpage (pageCheck_upper_head_position l p) hqHead).2
  have hlive : q.1.val ∈ live l p .upper := by
    by_contra hn
    exact hkeep (Finset.mem_sdiff.mpr ⟨haux, hn⟩)
  obtain ⟨a, hac, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp hlive)
  obtain ⟨hac, halevel⟩ := List.mem_filter.mp hac
  have halevel : 1 ≤ a.level ∧ a.level < p.levels := of_decide_eq_true halevel
  have hj_eq : a.level = j := by
    rcases lt_trichotomy a.level j with hlt | he | hgt
    · exact False.elim (canonical_upper_level_finished_empty l p hl hM haxes initial target hr ha hac
        halevel.1 halevel.2 n (by dsimp only [n]; omega) hq hax.symm)
    · exact he
    · have hpublic : a.privateColumn = false := by
        rcases pageColumn_public_or_first l p .upper hac with hp | hp
        · exact hp
        · omega
      have hbound := canonical_trim_retained_depth l p hl hM haxes initial target hr ha .upper hac hpublic
        (25 + n) (by simp only [ite_true]; omega) hqglobal hax.symm
      have hmono := PortLayout.Y_le p (show j + 1 ≤ a.level by omega)
      have hb := interlevelDepth_bounds p hj hjm
      simp only [pageDepth, interlevelRow, ite_true, hy] at hbound
      omega
  exact ⟨a, hac, hj_eq, hax.symm⟩

end PushPuzzle.Push.AcceptanceSoundness

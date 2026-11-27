/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideTerminal
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessSupportCut
import all Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgram

/-! Each actual public trim is bounded by its own preserved first interlevel or central flank marker. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- All original and added central markers remain present through both actual public trims. -/
private theorem canonical_central_marker_residual_five (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) :
    q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 5 := by
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have back (n : ℕ) (hn : 5 ≤ n)
      (h : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) n) :
      q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 5 := roundResidual_antitone _ _ _ hc hn h
  rcases central_sources l p hq with hy | hy | hy | ⟨hy, _⟩ | ⟨hy, _⟩
  · exact back 25 (by omega) (canonical_cut_residual_twentyfive l p hl hM haxes initial target hr ha hq hy)
  · exact back 10 (by omega) (flank_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hq (Or.inl hy))
  · exact back 10 (by omega) (flank_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hq (Or.inr hy))
  · exact back 12 (by omega) (guard_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hq hy)
  · exact back 22 (by omega) (sample_markers_residual l p hl hM haxes initial target hr
      (canonical_initial_frame l p hl hM haxes initial target)
      (canonical_initial_holes l p hl hM haxes initial target) ha hq hy)

/-- The first physical trim marker on every metadata column survives through the actual private-cap stage. -/
private theorem canonical_column_trim_marker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : Side) {a : PageColumn} (hac : a ∈ AcceptanceProgram.pageColumns l p side)
    (x : Fin (p.W + 1)) (hx : x.val = a.column) :
    ∃ g : Cell (p.W + 1) (p.H + 1), g.1 = x ∧ pageDepth p side g = trimDepth p a.level ∧
      g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) 10 := by
  obtain ⟨hj, hjm⟩ := l.acceptancePageColumn_level_bounds p hl hM side hac
  have haux : x.val ∈ auxiliaries l p := hx ▸ l.acceptancePageColumn_aux p hl hM haxes side hac
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hH : p.H = 2 * p.D := rfl
  by_cases hlevel : a.level < p.levels
  · have hb := interlevelDepth_bounds p hj hlevel
    let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨interlevelRow p side a.level, by
      cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] <;> omega⟩)
    have hy : g.2.val = interlevelRow p side a.level := rfl
    have hdepth : pageDepth p side g = trimDepth p a.level := by
      cases side <;> simp only [pageDepth, trimDepth, ite_eq_left hlevel, interlevelRow, interlevelDepth,
        reduceCtorEq, ite_false, ite_true, g]
      unfold interlevelDepth at hb
      omega
    have hm : InterlevelMarker l p side g := ⟨a, hac, hj, hlevel, hx, hdepth⟩
    have hinput := canonical_interlevel_marker_input l p hl hM haxes initial target hr ha side hj hlevel hm hy
    have hglobal : g ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (25 + interlevelIndex l p side a.level) := by
      rw [canonical_pageResidual_eq l p hl hM haxes initial target hr ha]
      exact hinput
    exact ⟨g, rfl, hdepth, roundResidual_antitone _ _ _ hc (by omega) hglobal⟩
  · have hD := p.outer_distance
    let g : Cell (p.W + 1) (p.H + 1) := (x, ⟨if side = .upper then p.D - 2 else p.D + 2, by split <;> omega⟩)
    have hrow : g.2.val = p.D - 2 ∨ g.2.val = p.D + 2 := by cases side <;> simp [g]
    have hg := auxiliary_flank_marker l p (q := g) haux hrow
    refine ⟨g, rfl, ?_, ?_⟩
    · cases side <;> simp only [pageDepth, trimDepth, ite_eq_right hlevel, reduceCtorEq, ite_false, ite_true, g]
      omega
    · exact flank_markers_residual l p hl hM haxes initial target hr
        (canonical_initial_frame l p hl hM haxes initial target)
        (canonical_initial_holes l p hl hM haxes initial target) ha (newCentralMarkers_subset l p hg) hrow

/-- A hole paid by a real public trim lies before its own certified first marker. -/
theorem canonical_trim_payment_depth (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : Side) {a : PageColumn} (hac : a ∈ AcceptanceProgram.pageColumns l p side)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = a.column)
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) (if side = .upper then 4 else 3))
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if side = .upper then 4 else 3) + 1)) :
    pageDepth p side q < trimDepth p a.level := by
  obtain ⟨g, hgx, hdepth, hg⟩ := canonical_column_trim_marker l p hl hM haxes initial target hr ha side hac q.1 hx
  let T := targetHoles l p target
  let stages := schedule l p (T \ Boundary.frame).card
  let i := if side = .upper then 4 else 3
  let dir : Direction := if side = .upper then .north else .south
  let requests := ((AcceptanceProgram.pageColumns l p side).filter fun a => !a.privateColumn).map fun a =>
    (a.column, trimDepth p a.level)
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[i]? = some (.read dir requests) := by
    cases side <;> simp only [i, stages, schedule, preparation, frameSchedule, trimRound,
      dir, requests, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hindex : i + 1 ≤ 10 := by cases side <;> simp [i]
  have hgAfter := roundResidual_antitone stages T (PushS.holes t) hc hindex hg
  have hlt := round_deleted_before_retained dir requests _ (roundResidual_step stages T (PushS.holes t) i hc hi).1
    hgAfter hq hqout (by cases side <;> simpa only [dir, ite_true, reduceCtorEq, ite_false, Direction.lane] using congrArg Fin.val hgx)
  have hrank : prefixRank dir g = trimDepth p a.level := by
    cases side <;> simpa only [dir, pageDepth, prefixRank, Nat.add_sub_cancel,
      ite_true, reduceCtorEq, ite_false] using hdepth
  cases side <;> simpa only [dir, pageDepth, prefixRank, Nat.add_sub_cancel,
    ite_true, reduceCtorEq, ite_false] using hlt.trans_le (le_of_eq hrank)

/-- Neither actual public trim uses any of the separately certified central markers as payment. -/
theorem canonical_trim_payment_not_central (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hqout : q ∉ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) ((if side = .upper then 4 else 3) + 1)) : q ∉ l.centralMarkers p := by
  intro hc
  have hres := canonical_central_marker_residual_five l p hl hM haxes initial target hr ha hc
  have hclean := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  apply hqout
  exact roundResidual_antitone _ _ _ hclean (by cases side <;> decide) hres

end PushPuzzle.Push.AcceptanceSoundness

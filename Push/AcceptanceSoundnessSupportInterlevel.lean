/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportUpperRowStock
public import Push.AcceptanceProgramInterlevelStockPrefix
import all Push.AcceptanceSoundnessSupportPagePositions
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgram

/-! Actual marker-row quota saturation certifies each emitted page/level marker in the accepted endpoint. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

private theorem interlevel_position (l : PortLayout) (p : Scales.Parameters) (side : PortLayout.Side)
    {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels) :
    (pageCheckStages l p)[interlevelIndex l p side j]? = some (readRows p .west {interlevelRow p side j}) := by
  cases side with
  | lower =>
    simpa only [interlevelIndex, interlevelRow, interlevelDepth, reduceCtorEq, ite_false, ite_true] using
      (pageCheck_lower_level_positions l p hj hjm).1
  | upper =>
    have he : (pageChecks l p .lower).length + 2 * j - 1 =
        (pageChecks l p .lower).length + (2 * j - 1) := by omega
    simpa only [interlevelIndex, interlevelRow, interlevelDepth, reduceCtorEq, ite_false, ite_true, he] using
      (pageCheck_upper_level_positions l p hj hjm).1

private theorem interlevel_actual_metadata (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : PortLayout.Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ pageResidual l p target (PushS.holes t) (interlevelIndex l p side j))
    (hy : q.2.val = interlevelRow p side j) :
    ∃ a ∈ pageColumns l p side, a.level = j ∧ q.1.val = a.column := by
  cases side with
  | lower =>
    exact canonical_lower_marker_input_metadata l p hl hM haxes initial target hr ha hj hjm hq hy
  | upper =>
    have he : interlevelIndex l p .upper j = (pageChecks l p .lower).length + (2 * j - 1) := by
      simp only [interlevelIndex, reduceCtorEq, ite_false]
      omega
    rw [he] at hq
    exact canonical_upper_marker_input_metadata l p hl hM haxes initial target hr ha hj hjm hq hy

/-- A real marker is present immediately before its matching actual horizontal check. -/
theorem canonical_interlevel_marker_input (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : PortLayout.Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q)
    (hy : q.2.val = interlevelRow p side j) :
    q ∈ pageResidual l p target (PushS.holes t) (interlevelIndex l p side j) := by
  let n := interlevelIndex l p side j
  let T := (emit (interlevelPrefix l p side j) (pageCheckTarget l p target)).remaining
  let E := pageResidual l p target (PushS.holes t) n
  have hc := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hstep := (roundResidual_step (pageCheckStages l p) (pageCheckTarget l p target) _ n hc
    (interlevel_position l p side hj hjm)).1
  have hread : Scan.Accepts (instructions (emit [readRows p .west {interlevelRow p side j}] T).rounds) E :=
    ⟨_, hstep⟩
  have hstock : (E.filter fun b => b.2.val ∈ ({interlevelRow p side j} : Finset ℕ)) ⊆
      T.filter fun b => b.2.val ∈ ({interlevelRow p side j} : Finset ℕ) := by
    intro b hb
    obtain ⟨hb, hby⟩ := Finset.mem_filter.mp hb
    have hby := Finset.mem_singleton.mp hby
    apply Finset.mem_filter.mpr
    exact ⟨(interlevel_target_row_iff l p hl hM haxes target side hj hjm hby).mpr
      (interlevel_actual_metadata l p hl hM haxes initial target hr ha side hj hjm hb hby),
      Finset.mem_singleton.mpr hby⟩
  have hsat := row_saturation p .west {interlevelRow p side j} (Or.inl rfl) T E hstock hread
  have hreference := interlevelMarker_prefix_remaining l p hl hM haxes target side hj hjm hm hy
  exact hsat (Finset.mem_filter.mpr ⟨hreference, Finset.mem_singleton.mpr hy⟩)

/-- Every actual emitted interlevel marker is a hole in the accepted terminal source configuration. -/
theorem canonical_interlevel_marker_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (side : PortLayout.Side) {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) : q ∈ PushS.holes t := by
  obtain ⟨a, hac, hj, hjm, hx, hd⟩ := hm
  have hm : InterlevelMarker l p side q := ⟨a, hac, hj, hjm, hx, hd⟩
  have hrow := marker_row p side hj hjm hd
  have hinput := canonical_interlevel_marker_input l p hl hM haxes initial target hr ha side hj hjm hm hrow
  have hc := (canonical_page_check_execution l p hl hM haxes initial target hr ha).2
  have hsub := scan_subset (roundResidual_eval (pageCheckStages l p) (pageCheckTarget l p target) _
    (interlevelIndex l p side a.level) hc) hinput
  have hcfull := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  exact scan_subset (roundResidual_eval (schedule l p (targetHoles l p target \ Boundary.frame).card)
    (targetHoles l p target) (PushS.holes t) 25 hcfull) hsub

end PushPuzzle.Push.AcceptanceSoundness

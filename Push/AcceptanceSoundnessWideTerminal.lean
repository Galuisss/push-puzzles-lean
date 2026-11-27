/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessWideSouth
import all PushS.PortWideFreeze
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgram

/-! Both real guard-column payments certify every physical wide separator hole. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- A physical wide separator on a selected guard column is a hole of the actual accepted endpoint. -/
private theorem canonical_selected_wide_separator_terminal (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {g : Cell (p.W + 1) (p.H + 1)} (hg : g ∈ l.wideSeparatorHoles p) (hx : g.1.val ∈ guards l p) : g ∈ PushS.holes t := by
  have htarget := wide_subset_encoded l p (l.canonical target) hg
  have hframe := l.wideSeparatorHoles_off_frame p hl hg
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  rcases lt_trichotomy g.2.val (p.D - 4) with hlt | heq | hgt
  · have hstock : g ∈ guardNorthStock l p target g.1.val :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htarget, hframe⟩, rfl, hlt⟩
    rw [canonical_wide_guard_north_paid l p hl hM haxes initial target hr ha hg hx] at hstock
    exact scan_subset (roundResidual_eval _ _ _ 11 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hstock).1).1
  · have hrow := (working_rows_iff l p g.2).mpr (l.wideSeparatorHoles_working_row p hg)
    have hgap := work_rows_central_gap l p hrow
    omega
  · have hstock : g ∈ guardSouthStock l p target g.1.val :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨htarget, hframe⟩, rfl, hgt⟩
    rw [canonical_wide_guard_south_paid l p hl hM haxes initial target hr ha hg hx] at hstock
    exact scan_subset (roundResidual_eval _ _ _ 19 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hstock).1).1

/-- Every emitted physical wide separator is a terminal hole on a source containing a real gate. -/
theorem canonical_wide_separators_terminal (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    (hgate : l.gateCenterCoordinates ≠ []) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    l.wideSeparatorHoles p ⊆ PushS.holes t := by
  intro g hg
  exact canonical_selected_wide_separator_terminal l p hl hM haxes initial target hr ha hg
    (l.wideSeparatorHoles_guard_of_gate p hl hgate hg)

end PushPuzzle.Push.AcceptanceSoundness

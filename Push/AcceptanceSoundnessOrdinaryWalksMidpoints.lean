/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessOrdinaryWalksStock
import all Push.AcceptanceSoundnessOrdinaryWalksStock
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessCentralRead
import all PushS.PortReaderFreeze

/-! Actual guard saturation and the reader radius bound protect every ordinary midpoint row. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

section Canonical
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)

/-- Actual north/south guard payments retain each reader midpoint once its reader-public walks stay empty. -/
private theorem canonical_reader_midpointRows_terminal_of_reader (j : ℕ) {t : State (p.W + 1)
    (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hR : ReaderWalkInvariant l p hl hM haxes initial target j t) :
    l.readerMidpointRows p j ⊆ PushS.holes t := by
  intro q hq
  obtain ⟨e, he, hej, hx, v, hv, _, hy⟩ := midpoint_data l p hq
  have hR' : ReaderWalkInvariant l p hl hM haxes initial target e.level t := by simpa only [hej] using hR
  have hg : q.1.val ∈ guards l p := hx ▸ l.endpoint_midpoint_guard p hl hM haxes e he
  have ht := midpoint_encoded l p hl hM (l.canonical target) hq
  have hf := midpoint_not_frame l p hl hM haxes hq
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hsource : ∀ r ∈ PushS.holes t, r ∉ Boundary.frame → r.1 = q.1 → r ∈ targetHoles l p target := by
    intro r hrhole _ hcol
    exact canonical_midpoint_column_target_stock_of_reader l p hl hM haxes initial target e he hr ha hR'
      ((congrArg Fin.val hcol).trans hx) hrhole
  rcases lt_trichotomy q.2.val (p.D - 4) with hlt | heq | hgt
  · have hstock : q ∈ guardNorthStock l p target q.1.val :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨ht, hf⟩, rfl, hlt⟩
    rw [canonical_guard_north_paid_of_target_stock l p hl hM haxes initial target hr ha q.1 hg hsource] at hstock
    exact scan_subset (roundResidual_eval _ _ _ 11 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hstock).1).1
  · have hrow := l.mem_workingRowSet_of_onSide p hv e.side q.2 hy
    have hgap := work_rows_central_gap l p ((working_rows_iff l p q.2).mpr hrow)
    omega
  · have hstock : q ∈ guardSouthStock l p target q.1.val :=
      Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨ht, hf⟩, rfl, hgt⟩
    rw [canonical_guard_south_paid_of_target_stock l p hl hM haxes initial target hr ha q.1 hg hsource] at hstock
    exact scan_subset (roundResidual_eval _ _ _ 19 hc) (Finset.mem_filter.mp (Finset.mem_sdiff.mp hstock).1).1

/-- Every selected-row midpoint is permanently empty and unvisited under the actual reader-walk invariant. -/
theorem canonical_reader_midpointRows_excluded_at_of_reader (j : ℕ) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial u)
    (hut : Reachable (l.canonicalInstance p hl hM haxes initial target).board none u t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    (hR : ReaderWalkInvariant l p hl hM haxes initial target j t) :
    Blocked.Excluded (l.readerMidpointRows p j) u := by
  have hsu' := canonical_reader_between_of_reader l p hl hM haxes initial target j .refl hsu hut ha hR
  have hut' := canonical_reader_between_of_reader l p hl hM haxes initial target j hsu hut .refl ha hR
  have hPi := hR _ .refl (hsu.trans hut)
  have hp : (l.canonicalInstance p hl hM haxes initial target).initial.player ∈ l.readerWalkHoles p j :=
    Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target)
  have hfinal := canonical_reader_midpointRows_terminal_of_reader l p hl hM haxes initial target j
    (hsu.trans hut) ha hR
  constructor
  · intro q hq
    exact Radius.distant_hole_at_from_exits
      (R := ReaderStep l p j (l.canonicalInstance p hl hM haxes initial target).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => reader_step_exit l p hl hM h hin hout)
      hsu' hut' hPi hp (midpoint_not_walk l p hl hM haxes hq)
      (midpoint_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hq) (hfinal hq)
  · intro hq
    exact Radius.player_ne_distant_from_exits
      (R := ReaderStep l p j (l.canonicalInstance p hl hM haxes initial target).board)
      (fun {_ _} h => h.1) (fun {_ _} h hin hout => reader_step_exit l p hl hM h hin hout)
      hsu' hPi hp (midpoint_not_walk l p hl hM haxes hq)
      (midpoint_actual_far l p hl hM haxes (l.canonical initial) (l.canonical target) hq) rfl

end Canonical
end PushPuzzle.Push.AcceptanceSoundness

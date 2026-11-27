/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockReads
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramNarrowSignals

/-! Every matching fixed midpoint marker survives the actual complete work prefix. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private def ReadAvoids {w h : ℕ} (q : Cell w h) : Template → Prop
  | .read side requests => q ∉ readRegion side requests
  | .clear _ _ => True

private theorem avoid_prefix_columns {p : Scales.Parameters} {q : Cell (p.W + 1) (p.H + 1)}
    (side : Direction) (hside : side = .north ∨ side = .south) (cols : Finset ℕ) (span : ℕ → ℕ)
    (hx : q.1.val ∉ cols) : q ∉ readRegion side (prefixRequests cols span) := by
  intro hread
  obtain ⟨⟨lane, count⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hread
  have hmem := ((mem_prefixRequests _ _ _ _).mp hreq).1
  have he : q.1.val = lane := by rcases hside with rfl | rfl <;> exact hcol
  exact hx (he.symm ▸ hmem)

private theorem avoid_whole_rows {p : Scales.Parameters} {q : Cell (p.W + 1) (p.H + 1)}
    (side : Direction) (hside : side = .west ∨ side = .east) (rows : Finset ℕ)
    (hy : q.2.val ∉ rows) : ReadAvoids q (readRows p side rows) :=
  fun hm => hy ((readRows_region p side rows hside q).mp hm)

private theorem work_reads_avoid (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (side : Side) {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) (k : ℕ) :
    ∀ stage ∈ workSchedule l p k, ReadAvoids q stage := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  have hm : InterlevelMarker l p side q := ⟨a, ha, hj, hjm, hx, hy⟩
  have haux := hx ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
  have haxis : q.1.val ∉ axes l p := fun h => (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ h)
  have hcore := l.acceptanceAux_not_core p hl haux
  have hguard := l.acceptanceAux_not_guard p haux
  have hrow := marker_row p side hj hjm hy
  have hbound := interlevelDepth_bounds p hj hjm
  have hh : p.H = 2 * p.D := rfl
  have hwork : q.2.val ∉ workRows l p := hrow ▸ interlevelRow_not_work l p side hj hjm
  have hprobe : q.2.val ∉ probeRows l p := fun h => hwork (probeRows_subset_workRows l p hl hM h)
  have hrows : q.2.val ∉ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at hrow <;> omega
  have hborder : q.1.val ≠ 0 ∧ q.1.val ≠ p.W := by
    have hn := (Finset.mem_sdiff.mp haux).2
    constructor <;> intro he <;> apply hn <;> apply Finset.mem_union_right
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he))
  have hntrimU := interlevelMarker_not_trim l p hl hM side .upper hm
  have hntrimL := interlevelMarker_not_trim l p hl hM side .lower hm
  have hnmainU := interlevelMarker_not_main l p hl hM haxes side .upper hm
  have hnmainL := interlevelMarker_not_main l p hl hM haxes side .lower hm
  have hnprivate := interlevelMarker_not_private l p hl side hm
  have hnsample := interlevelMarker_not_sample l p hl side hm
  have hnFrameColumns : ReadAvoids q (.read .south [(0, p.H + 1), (p.W, p.H + 1)]) := by
    intro hread
    obtain ⟨⟨lane, span⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hread
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
    change q.1.val = lane at hcol
    rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hborder.1 hcol
    · exact hborder.2 hcol
  have hnFrameRows : ReadAvoids q (.read .west [(0, p.W + 1), (p.H, p.W + 1)]) := by
    have hbd : q.2.val ≠ 0 ∧ q.2.val ≠ p.H := by
      cases side <;> simp only [interlevelRow, ite_true, reduceCtorEq, ite_false] at hrow <;> omega
    intro hread
    obtain ⟨⟨lane, span⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hread
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
    change q.2.val = lane at hcol
    rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hbd.1 hcol
    · exact hbd.2 hcol
  have hnGuardPrefix : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hguard
  have hnGuardFull : ReadAvoids q (readColumns p .south (guards l p)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hguard
  have hnCore : ReadAvoids q (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hcore
  have hnAxis : ReadAvoids q (axisReadRound l p) := by
    change q ∉ readRegion .north (_ ++ _)
    rw [readRegion_append]
    intro hread
    rcases Finset.mem_union.mp hread with hr | hr
    · exact avoid_prefix_columns .north (Or.inl rfl) _ _
        (fun hh => haxis (Finset.mem_sdiff.mp hh).1) hr
    · exact avoid_prefix_columns .north (Or.inl rfl) _ _ hcore hr
  have hnProbe : ReadAvoids q (readRows p .west (probeRows l p)) :=
    avoid_whole_rows .west (Or.inl rfl) _ hprobe
  have hnWork : ReadAvoids q (readRows p .west (workRows l p \ ({0, p.H} ∪ probeRows l p))) :=
    avoid_whole_rows .west (Or.inl rfl) _ (fun h => hwork (Finset.mem_sdiff.mp h).1)
  have hnFlanks : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) := by
    apply avoid_whole_rows .east (Or.inr rfl)
    intro h
    apply hrows
    rcases Finset.mem_insert.mp h with he | he
    · exact Finset.mem_insert.mpr (Or.inl he)
    · exact Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp he)))
  have hnMinus : ReadAvoids q (readRows p .west {p.D - 4}) :=
    avoid_whole_rows .west (Or.inl rfl) _ (fun h => hrows (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert.mpr (Or.inl (Finset.mem_singleton.mp h))))))
  have hnPlus : ReadAvoids q (readRows p .east {p.D + 4}) :=
    avoid_whole_rows .east (Or.inr rfl) _ (fun h => hrows (Finset.mem_insert_of_mem
      (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))))
  have htrimU : ReadAvoids q (trimRound l p .upper) := hntrimU
  have htrimL : ReadAvoids q (trimRound l p .lower) := hntrimL
  have hmainU : ReadAvoids q (mainRound l p .upper) := hnmainU
  have hmainL : ReadAvoids q (mainRound l p .lower) := hnmainL
  have hprivate : ReadAvoids q (privateRound l p) := hnprivate
  have hsample : ReadAvoids q (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) := hnsample
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  simp only [workSchedule, workReadSchedule, thirdRowSchedule, axisSchedule,
    preparation_eq_secondRows, secondRowSchedule, mainAxisSchedule, firstRowSchedule,
    firstTrimSchedule, markerPreparation, axisTail, workTail, frameSchedule,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false,
    true_and, hclear, htrimU, htrimL, hmainU, hmainL, hprivate, hsample, hnFrameColumns,
    hnFrameRows, hnGuardPrefix, hnGuardFull, hnCore, hnAxis, hnProbe, hnWork, hnFlanks, hnMinus, hnPlus]
  repeat' apply And.intro
  all_goals exact fun _ => trivial

/-- Every true midpoint marker survives all twenty-five actual canonical work-prefix blocks. -/
theorem interlevelMarker_work_remaining (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {q : Cell (p.W + 1) (p.H + 1)}
    (hm : InterlevelMarker l p side q) :
    q ∈ (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining := by
  apply emit_mem_of_no_reads _ _ (work_discarded_zero l p hl hM haxes target)
    (interlevelMarker_target l p hl hM target side hm)
  intro d requests hs
  exact work_reads_avoid l p hl hM haxes side hm _ (.read d requests) hs

end PushPuzzle.Push.AcceptanceProgram

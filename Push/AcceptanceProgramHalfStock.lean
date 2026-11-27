/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramHalfStockGeometry
import all Push.AcceptanceProgramHalfStockGeometry
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortStreetEnumeration

/-! Actual canonical half-depth inventory before the private cap and the later half-row check. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem half_frame_reads_avoid (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2)
    (hx : q.1.val ∈ cores l p ∪ privateColumns l p) :
    ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
  have hn := half_not_frame l p hl ha hy hx
  have hborder : q.1.val ≠ 0 ∧ q.1.val ≠ p.W ∧ q.2.val ≠ 0 ∧ q.2.val ≠ p.H := by
    constructor
    · intro he
      exact hn ((Boundary.mem_frame q).mpr ⟨.west, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] using he⟩)
    constructor
    · intro he
      exact hn ((Boundary.mem_frame q).mpr ⟨.east, by simp [Boundary.edge, he]⟩)
    constructor
    · intro he
      exact hn ((Boundary.mem_frame q).mpr ⟨.north, by simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, Fin.ext_iff] using he⟩)
    · intro he
      exact hn ((Boundary.mem_frame q).mpr ⟨.south, by simp [Boundary.edge, he]⟩)
  intro stage hs
  simp only [frameSchedule, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  all_goals intro hr
  all_goals obtain ⟨⟨lane, span⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hr
  all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
  · change q.1.val = lane at hcol
    rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hborder.1 hcol
    · exact hborder.2.1 hcol
  · change q.2.val = lane at hcol
    rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact hborder.2.2.1 hcol
    · exact hborder.2.2.2 hcol

/-- Both literal half markers survive the complete actual prefix preceding the private-cap read. -/
theorem half_before_private (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ cores l p ∪ privateColumns l p) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 9)
      (targetHoles l p target)).remaining := by
  have hs : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 9 =
      secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp [schedule, List.take_append, preparation_length, preparation_take_nine]
  rw [hs]
  apply emit_mem_of_no_reads _ _ (secondRows_discarded_zero l p hl hM ha target)
    (half_target l p target hy hx)
  have hframes := half_frame_reads_avoid l p hl ha hy hx
  have htrimU : ReadAvoids q (trimRound l p .upper) := half_not_trim l p hl hM .upper hy hx
  have htrimL : ReadAvoids q (trimRound l p .lower) := half_not_trim l p hl hM .lower hy hx
  have hmainU : ReadAvoids q (mainRound l p .upper) := half_not_main l p hl hM .upper hy hx
  have hmainL : ReadAvoids q (mainRound l p .lower) := half_not_main l p hl hM .lower hy hx
  have hall : ∀ stage ∈ secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card,
      ReadAvoids q stage := by
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false,
      true_and, htrimU, htrimL, hmainU, hmainL]
    repeat' apply And.intro
    all_goals first | exact hframes | exact fun _ => trivial | trivial
  exact fun side requests h => hall (.read side requests) h

private theorem core_not_guard (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {x : ℕ} (hx : x ∈ cores l p) : x ∉ guards l p := by
  apply l.acceptanceStreet_not_guard p
  change x ∈ ([0, p.W] ++ axisColumns l (coordinates p)) ++ originalAuxiliary l (coordinates p)
  exact List.mem_append_left _ (List.mem_append_right _
    (List.mem_toFinset.mp (l.acceptanceCore_subset_axes p hl hx)))

private theorem core_not_sample (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ cores l p) : x ∉ samples l p := by
  obtain ⟨i, hi, hix⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  intro hs
  obtain ⟨j, _, hxj⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hs)
  have hi' := center_columns_span p i (show x ∈ centerColumns p i from by
    rw [← hix]
    simp [centerColumns, coordinates, Coordinates.x, Scales.Parameters.x])
  have hj' : p.x j - columnRadius p ≤ x ∧ x ≤ p.x j + columnRadius p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj
    dsimp only [columnRadius]
    omega
  have he : i = j := column_owner p hi' hj'
  subst j
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hxj
  omega

private theorem core_work_remaining (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ cores l p) :
    q ∈ (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining := by
  have hx' := Finset.mem_union_left (privateColumns l p) hx
  apply emit_mem_of_no_reads _ _ (work_discarded_zero l p hl hM ha target)
    (half_target l p target hy hx')
  have hframe := half_frame_reads_avoid l p hl ha hy hx'
  have htrimU : ReadAvoids q (trimRound l p .upper) := half_not_trim l p hl hM .upper hy hx'
  have htrimL : ReadAvoids q (trimRound l p .lower) := half_not_trim l p hl hM .lower hy hx'
  have hmainU : ReadAvoids q (mainRound l p .upper) := half_not_main l p hl hM .upper hy hx'
  have hmainL : ReadAvoids q (mainRound l p .lower) := half_not_main l p hl hM .lower hy hx'
  have hnprivate : q.1.val ∉ privateColumns l p := fun hp =>
    l.acceptanceAux_not_core p hl (private_column_aux l p hl hM ha hp) hx
  have hprivate : ReadAvoids q (privateRound l p) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnprivate
  have hguard := core_not_guard l p hl hx
  have hsample := core_not_sample l p hx
  have hnGuardPrefix : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hguard
  have hnGuardFull : ReadAvoids q (readColumns p .south (guards l p)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hguard
  have hnSample : ReadAvoids q (.read .south (prefixRequests (samples l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hsample
  have hY := p.Y_ge 1
  have hD := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hD
  have hh : p.H = 2 * p.D := rfl
  have hwork : q.2.val ∉ workRows l p := hy ▸ halfRow_not_workRows l p
  have hprobe : q.2.val ∉ probeRows l p := fun h => hwork (probeRows_subset_workRows l p hl hM h)
  have hrows : q.2.val ∉ ({p.D - 2, p.D + 2, p.D - 4, p.D + 4} : Finset ℕ) := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hcorePrefix : ∀ n ≤ p.H - p.Y 1 + 1,
      q ∉ readRegion .north (prefixRequests (cores l p) fun _ => n) := by
    intro n hn hr
    obtain ⟨⟨lane, span⟩, hreq, _, hpos⟩ := (mem_readRegion _ _ q).mp hr
    have he := ((mem_prefixRequests _ _ lane span).mp hreq).2
    simp only [prefixRank] at hpos
    omega
  have hnAxis : ReadAvoids q (axisReadRound l p) := by
    change q ∉ readRegion .north (_ ++ _)
    rw [readRegion_append]
    intro hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact avoid_prefix_columns .north (Or.inl rfl) _ _
        (fun h => (Finset.mem_sdiff.mp h).2 hx) hr
    · exact hcorePrefix _ (by omega) hr
  have hnCore : ReadAvoids q (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) :=
    hcorePrefix _ le_rfl
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
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  have hall : ∀ stage ∈ workSchedule l p (targetHoles l p target \ Boundary.frame).card,
      ReadAvoids q stage := by
    simp only [workSchedule, workReadSchedule, thirdRowSchedule, axisSchedule,
      preparation_eq_secondRows, secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule]
    simp only [markerPreparation, axisTail, workTail, List.forall_mem_append,
      List.forall_mem_cons, List.not_mem_nil, forall_false]
    simp only [hclear, htrimU, htrimL, hmainU, hmainL, hprivate, hnAxis, hnCore]
    simp only [hnSample, hnGuardPrefix, hnGuardFull, hnProbe, hnWork, hnFlanks, hnMinus, hnPlus]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial | trivial
  exact fun side requests h => hall (.read side requests) h

/-- The core's literal half-depth marker survives to the actual half-row input at round 26. -/
theorem core_half_remaining (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ cores l p) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 26)
      (targetHoles l p target)).remaining := by
  have hs : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 26 =
      workSchedule l p (targetHoles l p target \ Boundary.frame).card ++
        [lowerFinish p (auxiliaries l p \ live l p .lower)] := by
    simp only [schedule, preparation, frameSchedule, workSchedule, workReadSchedule,
      thirdRowSchedule, thirdRowKeep, axisSchedule, axisTail, axisReadRound]
    simp only [workTail, pageChecks, List.cons_append, List.nil_append,
      List.take_succ_cons, List.take_zero, ite_true]
  rw [hs, emit_remaining_append, emit_remaining]
  simp only [allRegions, Finset.union_empty]
  apply Finset.mem_sdiff.mpr
  refine ⟨core_work_remaining l p hl hM ha target hy hx, ?_⟩
  exact avoid_prefix_columns .south (Or.inr rfl) _ _
    (fun h => l.acceptanceAux_not_core p hl (Finset.mem_sdiff.mp h).1 hx)

end PushPuzzle.Push.AcceptanceProgram

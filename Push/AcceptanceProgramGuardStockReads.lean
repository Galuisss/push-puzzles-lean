/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramGuardStockColumns
public import Push.AcceptanceProgramInterlevelStockReads
public import Push.AcceptanceProgramComplete
import all Push.AcceptanceSoundnessCentralGeometry
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! Exact canonical guard-column stock before the actual north and south guard reads. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout

private theorem guard_not_street (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ guards l p) : x ∉ l.streetColumnCoordinates p := by
  intro hs
  have hf := l.acceptanceGuard_street_far p hx hs
  rw [Nat.dist_self] at hf
  omega

private theorem guard_not_axis (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ guards l p) : x ∉ axes l p := by
  intro hs
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hs)
  exact guard_not_street l p hx (he ▸ axis_in_streetColumns l p (List.mem_range.mp hi))

private theorem frame_avoids (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hf : q ∉ Boundary.frame) : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
  have hq : q ∈ (emit (frameSchedule p.W p.H) Finset.univ).remaining := by
    rw [frame_remaining]
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hf⟩
  intro stage hs
  have hn := emit_stage_excluded hs hq
  cases stage with
  | read _ _ => exact hn
  | clear _ _ => trivial

private theorem take_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (n : ℕ) :
    (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take n)
      (targetHoles l p target)).discarded = 0 := by
  have hz := schedule_discarded_zero l p hl hM ha target
  rw [← List.take_append_drop n (schedule l p (targetHoles l p target \ Boundary.frame).card),
    emit_discarded_append] at hz
  omega

private theorem guard_column_reads_avoid (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hg : q.1.val ∈ guards l p) :
    (∀ side, ReadAvoids q (trimRound l p side)) ∧
      (∀ side, ReadAvoids q (mainRound l p side)) ∧ ReadAvoids q (privateRound l p) := by
  have hn := guard_not_street l p hg
  refine ⟨?_, ?_, ?_⟩
  · intro side hr
    obtain ⟨a, hc, _, hx, _⟩ := (mem_trim_region l p side q).mp hr
    exact hn (hx.symm ▸ PushPuzzle.Push.AcceptanceSoundness.acceptance_column_street l p hl hM ha side hc)
  · exact fun side hr => hn (PushPuzzle.Push.AcceptanceSoundness.main_column_street l p hl side hr)
  · exact fun hr => hn (PushPuzzle.Push.AcceptanceSoundness.private_column_street l p hl hM ha hr)

private theorem guard_before_north (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target \ Boundary.frame) (hg : q.1.val ∈ guards l p)
    (hy : q.2.val < p.D - 4) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 11)
      (targetHoles l p target)).remaining := by
  obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hq
  have hframe := frame_avoids p hf
  obtain ⟨htrim, hmain, hprivate⟩ := guard_column_reads_avoid l p hl hM ha hg
  have hflank : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) := by
    intro hr
    have hh := (readRows_region p .east _ (Or.inr rfl) q).mp hr
    simp only [Finset.mem_insert, Finset.mem_singleton] at hh
    omega
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  apply emit_mem_of_no_reads _ _ (take_discarded_zero l p hl hM ha target 11) ht
  have hs11 : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 11 =
      secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card ++
        [privateRound l p, readRows p .east {p.D - 2, p.D + 2}] := by
    simp only [schedule, preparation, frameSchedule, secondRowSchedule, mainAxisSchedule,
      firstRowSchedule, firstTrimSchedule, firstRowKeep, secondRowKeep]
    simp only [mainRound, mainTop, mainBottom, privateRound, privateColumns,
      ite_true, reduceCtorEq, ite_false]
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  have hall : ∀ stage ∈ (schedule l p (targetHoles l p target \ Boundary.frame).card).take 11,
      ReadAvoids q stage := by
    rw [hs11]
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false,
      hclear, htrim, hmain, hprivate, hflank, true_and]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial
  exact fun side requests hs => hall (.read side requests) hs

private theorem take_stock_interior (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (n : ℕ) (hn : 2 ≤ n) :
    (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take n)
      (targetHoles l p target)).remaining ⊆ targetHoles l p target \ Boundary.frame := by
  have hs : (schedule l p (targetHoles l p target \ Boundary.frame).card).take n =
      frameSchedule p.W p.H ++
        (((schedule l p (targetHoles l p target \ Boundary.frame).card).drop 2).take (n - 2)) := by
    cases n with
    | zero => omega
    | succ n => cases n with
      | zero => omega
      | succ n => simp only [schedule, preparation, frameSchedule, List.cons_append,
          List.nil_append, List.take_succ_cons, List.drop_succ_cons, List.drop_zero,
          show n + 1 + 1 - 2 = n from by omega]
  rw [hs, emit_remaining_append]
  exact (emit_remaining_subset _ _).trans (by rw [frame_remaining])

/-- The first actual north guard front is precisely the initial strict-interior stock above its marker. -/
theorem guard_north_front_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (x : ℕ) (hx : x ∈ guards l p) :
    (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 11)
      (targetHoles l p target)).remaining).filter fun q => q.1.val = x ∧ prefixRank .north q < p.D - 4) =
      (targetHoles l p target \ Boundary.frame).filter (fun q => q.1.val = x ∧ q.2.val < p.D - 4) := by
  apply Finset.ext
  intro q
  constructor
  · intro h
    obtain ⟨hq, hqx, hqy⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨take_stock_interior l p target 11 (by omega) hq, hqx, hqy⟩
  · intro h
    obtain ⟨hq, hqx, hqy⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr
      ⟨guard_before_north l p hl hM ha target hq (hqx ▸ hx) hqy, hqx, hqy⟩

private theorem guard_target_not_flank (l : PortLayout) (p : Scales.Parameters)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target \ Boundary.frame) (hg : q.1.val ∈ guards l p) :
    q.2.val ∉ ({p.D - 2, p.D + 2} : Finset ℕ) := by
  obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hq
  have hcol := guard_not_street l p hg
  have hD := p.outer_distance
  intro hr
  have hrow : q.2.val = p.D - 2 ∨ q.2.val = p.D + 2 := by
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hr
  have hlo : p.D ≤ q.2.val + 4 := by omega
  have hhi : q.2.val ≤ p.D + 4 := by omega
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp ht
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact hf (frame_contains (coordinates p) q ⟨s, hs, hc⟩)
    dsimp only [markedInterior] at hs
    simp only [List.mem_append, or_assoc] at hs
    rcases hs with hs | hs | hs | hs
    · have he : q.2.val = p.D := by
        split at hs
        · obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hs
          exact PushPuzzle.Push.AcceptanceSoundness.shifted_central_cut l p _ _ hold hc hlo hhi
        · exact PushPuzzle.Push.AcceptanceSoundness.base_central_cut l p hs hc hlo hhi
      omega
    · obtain ⟨x, hx, hs⟩ := List.mem_flatMap.mp hs
      have hstreet := (List.mem_filter.mp hx).1
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals
        have hcoord : q.1.val = x := (point_coordinates hc).1
        exact hcol (hcoord.symm ▸ hstreet)
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
      have he := (point_coordinates hc).2
      change q.2.val = p.D - 4 at he
      omega
    · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals have he := (point_coordinates hc).2
      all_goals change q.2.val = p.D + 4 at he
      all_goals omega
  · have hsig := l.signalSegments_central_gap p (l.canonical target)
      ((SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    omega

private theorem guard_before_south (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target \ Boundary.frame) (hg : q.1.val ∈ guards l p)
    (hy : p.D - 4 < q.2.val) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 19)
      (targetHoles l p target)).remaining := by
  obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp hq
  have hframe := frame_avoids p hf
  obtain ⟨htrim, hmain, hprivate⟩ := guard_column_reads_avoid l p hl hM ha hg
  have hflank : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) :=
    fun hr => guard_target_not_flank l p target hq hg ((readRows_region p .east _ (Or.inr rfl) q).mp hr)
  have hguard : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) := by
    intro hr
    obtain ⟨⟨lane, span⟩, hreq, _, hpos⟩ := (mem_readRegion _ _ q).mp hr
    have he := ((mem_prefixRequests _ _ lane span).mp hreq).2
    change q.2.val < span at hpos
    omega
  have hminus : ReadAvoids q (readRows p .west {p.D - 4}) := by
    intro hr
    have he := Finset.mem_singleton.mp ((readRows_region p .west _ (Or.inl rfl) q).mp hr)
    omega
  have hprobe : ReadAvoids q (readRows p .west (probeRows l p)) := by
    intro hr
    have he := (readRows_region p .west _ (Or.inl rfl) q).mp hr
    obtain ⟨e, he, hrow⟩ := List.mem_map.mp (List.mem_toFinset.mp he)
    obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
    have hb := readDepth_add_lt_D p e.level
    rw [readDepth_eq p hj hjm] at hb
    omega
  have haxis : q.1.val ∉ axes l p := guard_not_axis l p hg
  have hcore : q.1.val ∉ cores l p := fun hc => haxis (l.acceptanceCore_subset_axes p hl hc)
  have hnCore : ReadAvoids q (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hcore
  have hnAxis : ReadAvoids q (axisReadRound l p) := by
    change q ∉ readRegion .north (_ ++ _)
    rw [readRegion_append]
    intro hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact avoid_prefix_columns .north (Or.inl rfl) _ _ (fun h => haxis (Finset.mem_sdiff.mp h).1) hr
    · exact avoid_prefix_columns .north (Or.inl rfl) _ _ hcore hr
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  apply emit_mem_of_no_reads _ _ (take_discarded_zero l p hl hM ha target 19) ht
  have hs19 : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 19 =
      thirdRowSchedule l p (targetHoles l p target \ Boundary.frame).card ++
        [.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)] := by
    simp only [schedule, preparation, frameSchedule, thirdRowSchedule, thirdRowKeep,
      axisSchedule, axisTail, axisReadRound]
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  have hall : ∀ stage ∈ (schedule l p (targetHoles l p target \ Boundary.frame).card).take 19,
      ReadAvoids q stage := by
    rw [hs19]
    simp only [thirdRowSchedule, axisSchedule, preparation_eq_secondRows,
      secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule]
    simp only [markerPreparation, axisTail, List.forall_mem_append, List.forall_mem_cons,
      List.not_mem_nil, forall_false]
    simp only [hclear, htrim, hmain, hprivate, hflank, hguard, hminus, hprobe, hnAxis, hnCore]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial | trivial
  exact fun side requests hs => hall (.read side requests) hs

/-- The actual full south guard read sees exactly the original strict-interior stock below its marker. -/
theorem guard_south_stock_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (x : ℕ) (hx : x ∈ guards l p) :
    (((emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 19)
      (targetHoles l p target)).remaining).filter fun q => q.1.val = x) =
      (targetHoles l p target \ Boundary.frame).filter (fun q => q.1.val = x ∧ p.D - 4 < q.2.val) := by
  apply Finset.ext
  intro q
  constructor
  · intro h
    obtain ⟨hq, hqx⟩ := Finset.mem_filter.mp h
    have hi := take_stock_interior l p target 19 (by omega) hq
    have hsNorth : .read .north (prefixRequests (guards l p) fun _ => p.D - 4) ∈
        (schedule l p (targetHoles l p target \ Boundary.frame).card).take 19 := by
      simp only [schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.take_succ_cons, List.take_zero]
      iterate 11 apply List.mem_cons_of_mem
      exact List.mem_cons_self ..
    have hsRow : readRows p .west {p.D - 4} ∈
        (schedule l p (targetHoles l p target \ Boundary.frame).card).take 19 := by
      simp only [schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
        List.take_succ_cons, List.take_zero]
      iterate 12 apply List.mem_cons_of_mem
      exact List.mem_cons_self ..
    have hnorth := emit_stage_excluded hsNorth hq
    have hrow := emit_stage_excluded hsRow hq
    have hy : p.D - 4 < q.2.val := by
      by_contra he
      rcases lt_or_eq_of_le (Nat.le_of_not_gt he) with hlt | heq
      · apply hnorth
        exact (mem_readRegion _ _ q).mpr ⟨(x, p.D - 4),
          (mem_prefixRequests _ _ _ _).mpr ⟨hx, rfl⟩, hqx, hlt⟩
      · exact hrow ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr heq))
    exact Finset.mem_filter.mpr ⟨hi, hqx, hy⟩
  · intro h
    obtain ⟨hq, hqx, hqy⟩ := Finset.mem_filter.mp h
    exact Finset.mem_filter.mpr ⟨guard_before_south l p hl hM ha target hq (hqx ▸ hx) hqy, hqx⟩

end PushPuzzle.Push.AcceptanceProgram

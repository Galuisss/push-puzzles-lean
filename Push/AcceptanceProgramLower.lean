/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramWorkClear

/-! The actual lower-page checks are lossless and consume every lower and central marker. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Two literal read blocks before the lower gate-center clear. -/
def lowerHead (l : PortLayout) (p : Scales.Parameters) : List Template :=
  [lowerFinish p (auxiliaries l p \ live l p .lower), readRows p .west {p.H - p.Y 1 / 2}]

/-- All actual lower-page checks appended to the complete working-row prefix. -/
def lowerSchedule (l : PortLayout) (p : Scales.Parameters) (k : ℕ) : List Template :=
  workSchedule l p k ++ pageChecks l p .lower

private theorem lower_work_remaining {l : PortLayout} {p : Scales.Parameters} {k : ℕ}
    {E : Finset (Cell (p.W + 1) (p.H + 1))} {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (lowerSchedule l p k) E).remaining) : q ∈ (emit (workReadSchedule l p k) E).remaining := by
  rw [lowerSchedule, emit_remaining_append] at hq
  have hq := emit_remaining_subset _ _ hq
  rw [workSchedule, emit_remaining_append] at hq
  exact emit_remaining_subset _ _ hq

/-- The actual core clear, immediately after the half-depth read, has zero target loss. -/
private theorem target_lower_core_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    ((emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card ++ lowerHead l p)
      (targetHoles l p target)).remaining.filter fun q => Direction.north.lane q ∈ cores l p) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  change q.1.val ∈ cores l p at hx
  have hwork : q ∈ (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining := by
    rw [emit_remaining_append] at hq
    have hq := emit_remaining_subset _ _ hq
    rw [workSchedule, emit_remaining_append] at hq
    exact emit_remaining_subset _ _ hq
  cases workRead_inventory l p hl hM ha target hwork with
  | interlevel side hm =>
    obtain ⟨a, ha', _, _, he, _⟩ := hm
    exact l.acceptanceAux_not_core p hl (he.symm ▸ l.acceptancePageColumn_aux p hl hM ha side ha') hx
  | half hy hc =>
    have hs : readRows p .west {p.H - p.Y 1 / 2} ∈
        workSchedule l p (targetHoles l p target \ Boundary.frame).card ++ lowerHead l p := by
      apply List.mem_append_right
      unfold lowerHead
      exact .tail _ (.head _)
    exact emit_stage_excluded hs hq ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr hy))
  | cut hy hc => exact l.acceptanceAux_not_core p hl hc hx

/-- Every actual lower-page clear, including the gate-center clear, deletes zero target holes. -/
theorem lower_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (lowerSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  have hsplit : pageChecks l p .lower =
      (lowerHead l p ++ [.clear .north (cores l p)]) ++
      (List.range (p.levels - 1)).flatMap (fun k =>
        [readRows p .west {p.H - (p.Y (k + 1) + p.Y (k + 1 + 1)) / 2},
          lowerFinish p (levelColumns l p .lower (k + 1))]) := by
    simp only [pageChecks, lowerHead, ite_true, reduceCtorEq, ite_false, List.cons_append, List.nil_append]
  rw [lowerSchedule, hsplit, ← List.append_assoc, ← List.append_assoc, emit_discarded_append]
  have hprefix : (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card ++
      lowerHead l p ++ [.clear .north (cores l p)]) (targetHoles l p target)).discarded = 0 := by
    rw [emit_discarded_append]
    have hreads : (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card ++ lowerHead l p)
        (targetHoles l p target)).discarded = 0 := by
      rw [emit_discarded_append, work_discarded_zero l p hl hM ha target]
      simp only [lowerHead, lowerFinish, readRows, emit, Nat.add_zero]
    rw [hreads, Nat.zero_add]
    simp only [emit, Nat.add_zero]
    rw [target_lower_core_clear_empty l p hl hM ha target, Finset.card_empty]
  rw [hprefix, Nat.zero_add]
  apply emit_discarded_reads
  intro stage hs
  obtain ⟨j, _, hs⟩ := List.mem_flatMap.mp hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact ⟨.west, _, rfl⟩
  · exact ⟨.south, _, rfl⟩

private theorem lower_row_check (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    readRows p .west {p.H - (p.Y j + p.Y (j + 1)) / 2} ∈ pageChecks l p .lower := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have he : j - 1 + 1 = j := by omega
  simp only [he, ite_true]
  exact .head _

private theorem lower_column_finish (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    lowerFinish p (levelColumns l p .lower j) ∈ pageChecks l p .lower := by
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
  have he : j - 1 + 1 = j := by omega
  simp only [he, ite_true]
  exact .tail _ (.head _)

private theorem lowerFinish_cut (p : Scales.Parameters) (cols : Finset ℕ)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ cols) (hy : q.2.val = p.D) :
    q ∈ (lowerFinish p cols).region := by
  apply (mem_readRegion _ _ q).mpr
  refine ⟨(q.1.val, p.D + 1), (mem_prefixRequests _ _ _ _).mpr ⟨hx, rfl⟩, rfl, ?_⟩
  have hH : p.H = 2 * p.D := rfl
  simp only [prefixRank, Nat.add_sub_cancel]
  omega

/-- After all actual lower-page checks, every remaining target hole is an upper interlevel marker. -/
theorem lower_remaining_inventory (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (lowerSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining) : InterlevelMarker l p .upper q := by
  have hwork := lower_work_remaining hq
  have hnot (stage : Template) (hs : stage ∈ pageChecks l p .lower) : q ∉ stage.region :=
    emit_stage_excluded (List.mem_append_right _ hs) hq
  cases workRead_inventory l p hl hM ha target hwork with
  | interlevel side hm =>
    cases side
    · exact hm
    · obtain ⟨a, ha', hj, hjm, hx, hy⟩ := hm
      have hH0 := readDepth_add_lt_H p a.level
      have hH1 := readDepth_add_lt_H p (a.level + 1)
      rw [readDepth_eq p hj (by omega)] at hH0
      rw [readDepth_eq p (by omega) (by omega)] at hH1
      rw [trimDepth, ite_eq_left hjm] at hy
      have hy' : q.2.val = p.H - (p.Y a.level + p.Y (a.level + 1)) / 2 := by
        simp only [pageDepth, reduceCtorEq, ite_false] at hy
        have := q.2.isLt
        omega
      exact False.elim (hnot _ (lower_row_check l p hj hjm)
        ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr hy')))
  | half hy hx =>
    have hs : readRows p .west {p.H - p.Y 1 / 2} ∈ pageChecks l p .lower := by
      unfold pageChecks
      apply List.mem_append_left
      rw [ite_eq_left rfl]
      exact .tail _ (.head _)
    exact False.elim (hnot _ hs ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr hy)))
  | cut hy hx =>
    by_cases hLive : q.1.val ∈ live l p .lower
    · obtain ⟨a, ha', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hLive)
      obtain ⟨ha', hj⟩ := List.mem_filter.mp ha'
      have hj : 1 ≤ a.level ∧ a.level < p.levels := of_decide_eq_true hj
      have hcol : q.1.val ∈ levelColumns l p .lower a.level := by
        apply List.mem_toFinset.mpr
        apply List.mem_map.mpr
        exact ⟨a, List.mem_filter.mpr ⟨ha', by simp⟩, he⟩
      exact False.elim (hnot _ (lower_column_finish l p hj.1 hj.2) (lowerFinish_cut p _ hcol hy))
    · have hs : lowerFinish p (auxiliaries l p \ live l p .lower) ∈ pageChecks l p .lower := by
        unfold pageChecks
        apply List.mem_append_left
        rw [ite_eq_left rfl]
        exact .head _
      exact False.elim (hnot _ hs (lowerFinish_cut p _ (Finset.mem_sdiff.mpr ⟨hx, hLive⟩) hy))

end PushPuzzle.Push.AcceptanceProgram

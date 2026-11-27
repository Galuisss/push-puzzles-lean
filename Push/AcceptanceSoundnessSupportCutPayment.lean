/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCutResidual
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessSupportLanes
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceProgramRounds
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramComplete
import all Push.AcceptanceProgram

/-! The actual remaining central-cut hole is paid only by a genuine lower finishing read. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The actual page-check suffix after all twenty-five preparation and working-row blocks. -/
def pageCheckStages (l : PortLayout) (p : Scales.Parameters) : List Template :=
  pageChecks l p .lower ++ pageChecks l p .upper

/-- The canonical target residual passed to the real page-check suffix. -/
def pageCheckTarget (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card) (targetHoles l p target)).remaining

/-- The accepted actual stock after the twenty-five working blocks is cleanly exhausted by the page checks. -/
theorem canonical_page_check_execution (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) :
    Scan.eval (instructions (emit (pageCheckStages l p) (pageCheckTarget l p target)).rounds)
        (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
          (targetHoles l p target) (PushS.holes t) 25) = some ∅ ∧
      Scan.ClearsEmpty (instructions (emit (pageCheckStages l p) (pageCheckTarget l p target)).rounds)
        (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
          (targetHoles l p target) (PushS.holes t) 25) := by
  let T := targetHoles l p target
  let before := workSchedule l p (T \ Boundary.frame).card
  have hsplit : schedule l p (T \ Boundary.frame).card = before ++ pageCheckStages l p := by
    simp only [before, schedule, workSchedule, workReadSchedule, thirdRowSchedule,
      axisSchedule, axisTail, workTail, axisReadRound, thirdRowKeep, pageCheckStages, List.append_assoc,
      List.cons_append, List.nil_append]
  have hclean := program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha
  have hfull := hclean.1
  have hc := hclean.2
  unfold program at hc hfull
  rw [hsplit, emit_rounds_append, instructions, List.flatMap_append] at hc hfull
  obtain ⟨F, hF, _, hafter⟩ := clean_append _ _ (PushS.holes t) hc
  rw [eval_append, hF, Option.bind_some] at hfull
  have htake : (schedule l p (T \ Boundary.frame).card).take 25 = before := schedule_take_twentyfive l p _
  have hres := roundResidual_eval (schedule l p (T \ Boundary.frame).card) T (PushS.holes t) 25 hclean.2
  rw [htake] at hres
  have hF' : F = roundResidual (schedule l p (T \ Boundary.frame).card) T (PushS.holes t) 25 :=
    Option.some.inj (hF.symm.trans hres)
  subst F
  exact ⟨hfull, hafter⟩

private theorem level_rows_not_cut (p : Scales.Parameters) {j : ℕ} (hj : j ∈ List.range (p.levels - 1)) :
    (p.Y (j + 1) + p.Y (j + 1 + 1)) / 2 ≠ p.D ∧
      p.H - (p.Y (j + 1) + p.Y (j + 1 + 1)) / 2 ≠ p.D := by
  have hj' := List.mem_range.mp hj
  have h₁ := readDepth_le_last p (j + 1)
  have h₂ := readDepth_le_last p (j + 1 + 1)
  rw [readDepth_eq p (by omega) (by omega)] at h₁ h₂
  have hD := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at hD
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem page_cut_payment_shape (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {side : Direction} {requests : List (ℕ × ℕ)}
    (hstage : Template.read side requests ∈ pageCheckStages l p)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.D)
    (ht : ReadTouches (.read side requests) q) :
    side = .south ∧ ∃ cols : Finset ℕ, requests = prefixRequests cols (fun _ => p.D + 1) ∧ cols ⊆ auxiliaries l p := by
  have hY := readDepth_le_last p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hY
  have hD := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at hD
  have hH : p.H = 2 * p.D := rfl
  simp only [pageCheckStages, pageChecks, ite_true, reduceCtorEq, ite_false, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hstage
  rcases hstage with (hhead | hlevels) | (hhead | hlevels)
  · rcases hhead with he | he
    · cases he
      exact ⟨rfl, _, rfl, Finset.sdiff_subset⟩
    · cases he
      have hrow := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
      omega
  · obtain ⟨j, hj, hmem⟩ := List.mem_flatMap.mp hlevels
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with he | he
    · cases he
      have hrow := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
      exact ((level_rows_not_cut p hj).2 (hrow.symm.trans hy)).elim
    · cases he
      refine ⟨rfl, _, rfl, ?_⟩
      intro x hx
      obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact he ▸ l.acceptancePageColumn_aux p hl hM haxes .lower (List.mem_filter.mp ha).1
  · exact hhead.elim
  · obtain ⟨j, hj, hmem⟩ := List.mem_flatMap.mp hlevels
    simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq] at hmem
    cases hmem
    have hrow := Finset.mem_singleton.mp (row_touches p .west _ (Or.inl rfl) ht)
    exact ((level_rows_not_cut p hj).1 (hrow.symm.trans hy)).elim

/-- Each old central marker has a genuine page-suffix payment, whose deleting read is a lower finishing read on auxiliary columns. -/
theorem canonical_cut_payment_lower (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p) (hy : q.2.val = p.D) :
    ∃ pay : RoundPayment (pageCheckStages l p) (pageCheckTarget l p target)
        (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
          (targetHoles l p target) (PushS.holes t) 25) q,
      pay.side = .south ∧ ∃ cols : Finset ℕ,
        pay.requests = prefixRequests cols (fun _ => p.D + 1) ∧ cols ⊆ auxiliaries l p := by
  have he := canonical_page_check_execution l p hl hM haxes initial target hr ha
  obtain ⟨pay⟩ := round_payment (pageCheckStages l p) _ _ he.1 he.2
    (canonical_cut_residual_twentyfive l p hl hM haxes initial target hr ha hq hy)
  have hstage : Template.read pay.side pay.requests ∈ pageCheckStages l p := by
    have hm : Template.read pay.side pay.requests ∈ pay.before ++ Template.read pay.side pay.requests :: pay.after :=
      List.mem_append_right _ List.mem_cons_self
    exact (congrArg (fun stages : List Template => Template.read pay.side pay.requests ∈ stages) pay.split).mpr hm
  exact ⟨pay, page_cut_payment_shape l p hl hM haxes hstage hy pay.on_line⟩

end PushPuzzle.Push.AcceptanceSoundness

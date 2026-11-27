/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportHalfStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramLower
import all Push.AcceptanceProgramComplete
import all Push.AcceptanceProgram
import all Push.AcceptanceSoundnessCentral

/-! Literal positions of the actual layered page checks. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The actual residual at a page-suffix boundary, after all twenty-five working blocks. -/
def pageResidual (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (n : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  roundResidual (pageCheckStages l p) (pageCheckTarget l p target)
    (roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) E 25) n

/-- Page-suffix residuals are the literal later residuals of the same real complete execution. -/
theorem canonical_pageResidual_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t)) (n : ℕ) :
    roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target) (PushS.holes t) (25 + n) = pageResidual l p target (PushS.holes t) n := by
  let T := targetHoles l p target
  let left := workSchedule l p (T \ Boundary.frame).card
  have hs : schedule l p (T \ Boundary.frame).card = left ++ pageCheckStages l p := by
    rw [schedule_eq_lower_upper, lowerSchedule, List.append_assoc]
    rfl
  have hlen : left.length = 25 := by
    have h := congrArg List.length (schedule_take_twentyfive l p (T \ Boundary.frame).card)
    rw [List.length_take, schedule_length] at h
    change min 25 (4 * p.levels + 25) = left.length at h
    omega
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  change Scan.ClearsEmpty (instructions (emit (schedule l p (T \ Boundary.frame).card) T).rounds) (PushS.holes t) at hc
  rw [hs] at hc
  have he := roundResidual_append left (pageCheckStages l p) T (PushS.holes t) n hc
  rw [hlen, ← hs] at he
  exact he

private theorem paired_get {α β : Type*} (f g : α → β) (xs : List α) (i : ℕ) (a : α)
    (hi : xs[i]? = some a) :
    (xs.flatMap fun x => [f x, g x])[2 * i]? = some (f a) ∧
      (xs.flatMap fun x => [f x, g x])[2 * i + 1]? = some (g a) := by
  induction xs generalizing i with
  | nil => simp only [List.getElem?_nil] at hi; contradiction
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst a
      simp
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      have h := ih i hi
      simpa only [show 2 * (i + 1) = 2 * i + 2 by omega,
        show 2 * i + 2 + 1 = (2 * i + 1) + 2 by omega, List.flatMap_cons,
        List.cons_append, List.nil_append, List.getElem?_cons_succ] using h

/-- The lower marker row is followed immediately by its own literal southward finishing block. -/
theorem pageCheck_lower_level_positions (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    (pageCheckStages l p)[2 * j + 1]? = some (readRows p .west {p.H - (p.Y j + p.Y (j + 1)) / 2}) ∧
      (pageCheckStages l p)[2 * j + 2]? =
        some (.read .south (prefixRequests (lowerLevelColumns l p j) fun _ => p.D + 1)) := by
  have hfirst := paired_get
    (fun k => readRows p .west {p.H - (p.Y (k + 1) + p.Y (k + 2)) / 2})
    (fun k => lowerFinish p (levelColumns l p .lower (k + 1)))
    (List.range (p.levels - 1)) (j - 1) (j - 1) (List.getElem?_range (by omega))
  have hi : 2 * j + 1 = 2 * (j - 1) + 3 := by omega
  have hi' : 2 * j + 2 = (2 * (j - 1) + 1) + 3 := by omega
  have hj' : j - 1 + 1 = j := by omega
  have hj'' : j - 1 + 2 = j + 1 := by omega
  have hleft : 2 * j + 2 < (pageChecks l p .lower).length := by
    rw [pageChecks_length]
    simp only [ite_true]
    omega
  rw [pageCheckStages, List.getElem?_append_left (by omega), List.getElem?_append_left hleft]
  change (lowerFinish p (auxiliaries l p \ live l p .lower) :: readRows p .west {p.H - p.Y 1 / 2} ::
    .clear .north (cores l p) :: _)[2 * j + 1]? = _ ∧
      (lowerFinish p (auxiliaries l p \ live l p .lower) :: readRows p .west {p.H - p.Y 1 / 2} ::
        .clear .north (cores l p) :: _)[2 * j + 2]? = _
  simp only [hi, hi', List.getElem?_cons_succ]
  simpa [hj', hj'', lowerFinish, lowerLevelColumns, levelColumns, Nat.add_assoc] using hfirst

private theorem pageCheck_upper_level_positions (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    (pageCheckStages l p)[(pageChecks l p .lower).length + (2 * j - 1)]? =
        some (readRows p .west {(p.Y j + p.Y (j + 1)) / 2}) ∧
      (pageCheckStages l p)[(pageChecks l p .lower).length + 2 * j]? =
        some (.clear .north (levelColumns l p .upper j)) := by
  have hfirst := paired_get
    (fun k => readRows p .west {(p.Y (k + 1) + p.Y (k + 2)) / 2})
    (fun k => Template.clear .north (levelColumns l p .upper (k + 1)))
    (List.range (p.levels - 1)) (j - 1) (j - 1) (List.getElem?_range (by omega))
  rw [pageCheckStages, List.getElem?_append_right (by omega),
    List.getElem?_append_right (by omega), Nat.add_sub_cancel_left, Nat.add_sub_cancel_left]
  change (Template.clear .north (auxiliaries l p \ live l p .upper) :: _)[2 * j - 1]? = _ ∧
    (Template.clear .north (auxiliaries l p \ live l p .upper) :: _)[2 * j]? = _
  have hi' : 2 * j = (2 * (j - 1) + 1) + 1 := by omega
  simp only [hi', List.getElem?_cons_succ]
  have hj' : j - 1 + 1 = j := by omega
  have hj'' : j - 1 + 2 = j + 1 := by omega
  simpa [hj', hj'', Nat.add_assoc] using hfirst

private theorem pageCheck_upper_head_position (l : PortLayout) (p : Scales.Parameters) :
    (pageCheckStages l p)[(pageChecks l p .lower).length]? =
      some (.clear .north (auxiliaries l p \ live l p .upper)) := by
  rw [pageCheckStages, List.getElem?_append_right le_rfl, Nat.sub_self]
  rfl

end PushPuzzle.Push.AcceptanceSoundness

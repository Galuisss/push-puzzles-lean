/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportClean
import all Push.AcceptanceSoundnessSupportRounds
import all Push.AcceptanceSoundnessCentralRead
import all Push.AcceptanceSoundnessFrame
import all Push.AcceptanceProgramRounds

/-! Deterministic actual residuals at every compact-round boundary of a clean scan execution. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS AcceptanceProgram

/-- The actual scan residual after the first n compact rounds. -/
def roundResidual {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ) : Finset (Cell w h) :=
  (Scan.eval (instructions (emit (stages.take n) T).rounds) E).getD ∅

theorem roundResidual_eval {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) :
    Scan.eval (instructions (emit (stages.take n) T).rounds) E = some (roundResidual stages T E n) := by
  rw [← List.take_append_drop n stages, emit_rounds_append, instructions, List.flatMap_append] at hc
  obtain ⟨F, hF, _, _⟩ := clean_append _ _ E hc
  change Scan.eval (instructions (emit (stages.take n) T).rounds) E = some F at hF
  unfold roundResidual
  rw [hF]
  rfl

theorem roundResidual_clean {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) :
    Scan.ClearsEmpty (instructions (emit (stages.take n) T).rounds) E := by
  rw [← List.take_append_drop n stages, emit_rounds_append, instructions, List.flatMap_append] at hc
  exact (clean_append _ _ E hc).choose_spec.2.1

/-- Each actual residual transition is the emitted round at that literal schedule position. -/
theorem roundResidual_step {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) {stage : Template}
    (hi : stages[n]? = some stage) :
    Scan.eval (instructions (emit [stage] (emit (stages.take n) T).remaining).rounds)
        (roundResidual stages T E n) = some (roundResidual stages T E (n + 1)) ∧
      Scan.ClearsEmpty (instructions (emit [stage] (emit (stages.take n) T).remaining).rounds)
        (roundResidual stages T E n) := by
  have htake : stages.take (n + 1) = stages.take n ++ [stage] := by
    rw [List.take_add_one, hi]
    rfl
  have hcn := roundResidual_clean stages T E (n + 1) hc
  have hen := roundResidual_eval stages T E (n + 1) hc
  rw [htake, emit_rounds_append, instructions, List.flatMap_append] at hcn hen
  obtain ⟨F, hF, _, hstage⟩ := clean_append _ _ E hcn
  have hprefix := roundResidual_eval stages T E n hc
  simp only [instructions] at hprefix
  have heq : F = roundResidual stages T E n := Option.some.inj (hF.symm.trans hprefix)
  subst F
  rw [eval_append, hprefix, Option.bind_some] at hen
  exact ⟨hen, hstage⟩

/-- A zero-loss clear preserves every current actual hole. -/
theorem roundResidual_clear_keeps {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E)
    {side : Direction} {lanes : Finset ℕ} (hi : stages[n]? = some (.clear side lanes))
    {q : Cell w h} (hq : q ∈ roundResidual stages T E n) :
    q ∈ roundResidual stages T E (n + 1) ∧ side.lane q ∉ lanes := by
  have hs := roundResidual_step stages T E n hc hi
  obtain ⟨F, hF, hclear, _⟩ := hs.2
  have heq : F = roundResidual stages T E (n + 1) := Option.some.inj (hF.symm.trans hs.1)
  have hkeep := hclear q hq
  have hf : q ∈ F := (Option.some.inj hF) ▸ Finset.mem_filter.mpr ⟨hq, hkeep⟩
  exact ⟨heq ▸ hf, hkeep⟩

/-- A round whose whole read lines avoid a hole preserves that actual hole. -/
theorem roundResidual_unread_keeps {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) {stage : Template}
    (hi : stages[n]? = some stage) {q : Cell w h} (hq : q ∈ roundResidual stages T E n)
    (ht : ¬ReadTouches stage q) : q ∈ roundResidual stages T E (n + 1) := by
  have hs := roundResidual_step stages T E n hc hi
  exact clean_unread_survives [stage] _ _ _ hs.2 hs.1 hq (by
    intro s hs
    cases List.mem_singleton.mp hs
    exact ht)

theorem roundResidual_succ_subset {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) :
    roundResidual stages T E (n + 1) ⊆ roundResidual stages T E n := by
  cases hi : stages[n]? with
  | some stage => exact scan_subset (roundResidual_step stages T E n hc hi).1
  | none =>
    have he : stages.take (n + 1) = stages.take n := by simp only [List.take_add_one, hi, Option.toList_none, List.append_nil]
    unfold roundResidual
    rw [he]

/-- Actual destructive residuals decrease with the compact-round index. -/
theorem roundResidual_antitone {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h))
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E) {n m : ℕ} (hnm : n ≤ m) :
    roundResidual stages T E m ⊆ roundResidual stages T E n := by
  induction m with
  | zero =>
    have hn : n = 0 := by omega
    subst n
    exact Finset.Subset.refl _
  | succ m ih =>
    by_cases hn : n ≤ m
    · exact (roundResidual_succ_subset stages T E m hc).trans (ih hn)
    · have he : n = m + 1 := by omega
      subst n
      exact Finset.Subset.refl _

/-- A hole beyond a marker retained at a later round cannot be paid by the current same-direction read. -/
theorem roundResidual_marker_keeps {w h : ℕ} (stages : List Template) (T E : Finset (Cell w h)) (n later : ℕ)
    (hc : Scan.ClearsEmpty (instructions (emit stages T).rounds) E)
    {side : Direction} {requests : List (ℕ × ℕ)} (hi : stages[n]? = some (.read side requests))
    {a b : Cell w h} (ha : a ∈ roundResidual stages T E later) (hindex : n + 1 ≤ later)
    (hb : b ∈ roundResidual stages T E n) (hlane : side.lane a = side.lane b)
    (hrank : prefixRank side a ≤ prefixRank side b) : b ∈ roundResidual stages T E (n + 1) := by
  by_contra hnot
  have ha' := roundResidual_antitone stages T E hc hindex ha
  have hlt := round_deleted_before_retained side requests _
    (roundResidual_step stages T E n hc hi).1 ha' hb hnot hlane
  omega

/-- A genuine payment's input is the deterministic residual at its actual prefix length. -/
theorem RoundPayment.input_roundResidual {w h : ℕ} {stages : List Template} {T E : Finset (Cell w h)}
    {q : Cell w h} (pay : RoundPayment stages T E q) :
    pay.input = roundResidual stages T E pay.before.length := by
  have htake : stages.take pay.before.length = pay.before := by
    simpa using congrArg (List.take pay.before.length) pay.split
  unfold roundResidual
  rw [htake, pay.prefix_eval]
  rfl

/-- A genuine payment's output is the deterministic residual immediately after its read round. -/
theorem RoundPayment.output_roundResidual {w h : ℕ} {stages : List Template} {T E : Finset (Cell w h)}
    {q : Cell w h} (pay : RoundPayment stages T E q) :
    pay.output = roundResidual stages T E (pay.before.length + 1) := by
  have htake : stages.take (pay.before.length + 1) = pay.before ++ [.read pay.side pay.requests] := by
    simpa [List.take_append, List.take_of_length_le (show pay.before.length ≤ pay.before.length + 1 by omega)] using
      congrArg (List.take (pay.before.length + 1)) pay.split
  unfold roundResidual
  rw [htake, pay.output_eval]
  rfl

/-- A literal compact prefix may be executed once before taking residuals in its suffix. -/
theorem roundResidual_append {w h : ℕ} (before after : List Template) (T E : Finset (Cell w h))
    (n : ℕ) (hc : Scan.ClearsEmpty (instructions (emit (before ++ after) T).rounds) E) :
    roundResidual (before ++ after) T E (before.length + n) =
      roundResidual after (emit before T).remaining
        (roundResidual (before ++ after) T E before.length) n := by
  have hleft := roundResidual_eval (before ++ after) T E before.length hc
  simp only [List.take_left] at hleft
  unfold roundResidual
  rw [List.take_append, Nat.add_sub_cancel_left]
  simp only [Nat.le_add_right, List.take_of_length_le]
  rw [emit_rounds_append, instructions, List.flatMap_append, eval_append]
  simp only [instructions] at hleft
  rw [hleft, Option.bind_some]
  rfl

end PushPuzzle.Push.AcceptanceSoundness

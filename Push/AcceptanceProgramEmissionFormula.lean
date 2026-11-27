/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramRegions
import Mathlib.Data.List.GetD

/-! Exact finite-prefix formulas for every quota of the actual compact emitter. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS

/-- The literal compact round emitted by one actual stage on its current target stock. -/
@[expose] def emitRound {w h : ℕ} (stage : Template) (E : Finset (Cell w h)) : Round :=
  match stage with
  | .read side requests => .read side (emitReads side requests E).quotas
  | .clear side lanes => .clear side lanes

private theorem emit_rounds_cons {w h : ℕ} (stage : Template) (rest : List Template) (E : Finset (Cell w h)) :
    (emit (stage :: rest) E).rounds = emitRound stage E :: (emit rest (emit [stage] E).remaining).rounds := by
  cases stage <;> rfl

/-- Each compact output round is computed on exactly the target remaining after its literal prior templates. -/
theorem emit_round_at {w h : ℕ} (stages : List Template) (E : Finset (Cell w h)) (i : ℕ)
    (hi : i < stages.length) :
    (emit stages E).rounds.getD i (.read .north []) =
      emitRound (stages.getD i (.read .north [])) (emit (stages.take i) E).remaining := by
  induction stages generalizing i E with
  | nil => simp only [List.length_nil] at hi; omega
  | cons stage rest ih =>
    cases i with
    | zero => rw [emit_rounds_cons]; rfl
    | succ i =>
      have hir : i < rest.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
      rw [emit_rounds_cons, List.getD_cons_succ, ih _ i hir, List.getD_cons_succ, List.take_succ_cons]
      rw [show stage :: rest.take i = [stage] ++ rest.take i from rfl, emit_remaining_append]

/-- Literal same-direction prefix regions compose by deleting their union from the same target. -/
private theorem emitReads_remaining_append {w h : ℕ} (side : Direction) (left right : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    (emitReads side (left ++ right) E).remaining =
      (emitReads side right (emitReads side left E).remaining).remaining := by
  simp only [emitReads_remaining, readRegion_append]
  ext q
  simp only [Finset.mem_sdiff, Finset.mem_union]
  tauto

/-- Every output lane quota counts the actual target holes after the preceding requests of its round. -/
private theorem emitReads_quota_at {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) (i : ℕ) (hi : i < requests.length) :
    (emitReads side requests E).quotas.getD i (0, 0) =
      let request := requests.getD i (0, 0)
      (request.1, ((emitReads side (requests.take i) E).remaining.filter fun q =>
        q ∈ (Scan.lineCells side request.1).take request.2).card) := by
  induction requests generalizing i E with
  | nil => simp only [List.length_nil] at hi; omega
  | cons request rest ih =>
    cases i with
    | zero => rfl
    | succ i =>
      have hir : i < rest.length := by simpa only [List.length_cons, Nat.add_lt_add_iff_right] using hi
      rcases request with ⟨lane, span⟩
      simp only [emitReads, List.getD_cons_succ]
      rw [ih _ i hir, List.take_succ_cons]
      rw [show (lane, span) :: rest.take i = [(lane, span)] ++ rest.take i from rfl,
        emitReads_remaining_append]
      rfl

/-- Every actual request contributes exactly one lane/quota pair. -/
private theorem emitReads_quotas_length {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) : (emitReads side requests E).quotas.length = requests.length := by
  induction requests generalizing E with
  | nil => rfl
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    simp only [emitReads, List.length_cons, ih]

/-- Every request counts the initial target holes not already touched by prior rounds or requests. -/
@[expose] def quotaRequests {w h : ℕ} (before : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (E : Finset (Cell w h)) : List (ℕ × ℕ) :=
  requests.mapIdx fun i request => (request.1,
    (E.filter fun q => q ∉ allRegions before ∧ q ∉ readRegion side (requests.take i) ∧
      q ∈ (Scan.lineCells side request.1).take request.2).card)

/-- The finite-prefix quota formula is exactly the real stateful read emitter. -/
private theorem emitReads_quotas_formula {w h : ℕ} (before : List Template) (side : Direction)
    (requests : List (ℕ × ℕ)) (E : Finset (Cell w h)) :
    (emitReads side requests (emit before E).remaining).quotas = quotaRequests before side requests E := by
  apply List.ext_getElem (by simp only [emitReads_quotas_length, quotaRequests, List.length_mapIdx])
  intro i hi hi'
  have hir : i < requests.length := by simpa only [emitReads_quotas_length] using hi
  rw [← List.getD_eq_getElem _ (0, 0) hi, emitReads_quota_at side requests _ i hir]
  simp only [quotaRequests, List.getElem_mapIdx, List.getD_eq_getElem requests (0, 0) hir,
    emitReads_remaining, emit_remaining]
  apply congrArg (fun F : Finset (Cell w h) => ((requests[i]).1, F.card))
  ext q
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  tauto

/-- A complete round emitted by finite-prefix target tests. -/
@[expose] def formulaRound {w h : ℕ} (before : List Template) (stage : Template) (E : Finset (Cell w h)) : Round :=
  match stage with
  | .read side requests => .read side (quotaRequests before side requests E)
  | .clear side lanes => .clear side lanes

/-- Every actual stateful round equals its direct finite-prefix formula. -/
private theorem emitRound_formula {w h : ℕ} (before : List Template) (stage : Template) (E : Finset
    (Cell w h)) :
    emitRound stage (emit before E).remaining = formulaRound before stage E := by
  cases stage with
  | read side requests => exact congrArg (Round.read side) (emitReads_quotas_formula before side requests E)
  | clear => rfl

/-- The whole compact round list computed directly from the original target and literal prefix regions. -/
@[expose] def formulaRounds {w h : ℕ} (stages : List Template) (E : Finset (Cell w h)) : List Round :=
  stages.mapIdx fun i stage => formulaRound (stages.take i) stage E

/-- The complete finite-prefix formula emits precisely the existing actual compact program. -/
theorem emit_rounds_formula {w h : ℕ} (stages : List Template) (E : Finset (Cell w h)) :
    (emit stages E).rounds = formulaRounds stages E := by
  apply List.ext_getElem (by simp only [emit_rounds_length, formulaRounds, List.length_mapIdx])
  intro i hi hi'
  have hir : i < stages.length := by simpa only [emit_rounds_length] using hi
  rw [← List.getD_eq_getElem _ (.read .north []) hi, emit_round_at stages E i hir]
  simp only [formulaRounds, List.getElem_mapIdx, List.getD_eq_getElem stages (.read .north []) hir]
  exact emitRound_formula _ _ _

end PushPuzzle.Push.AcceptanceProgram

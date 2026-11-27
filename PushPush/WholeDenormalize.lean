/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeNormalize

/-! Exact dense reads recover sparse whole cuts when positive requests have distinct lanes. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell Direction)

variable {w h : ℕ}

private theorem eval_drop_zero (side : Direction) (requests : List (ℕ × ℕ))
    (E : Finset (Cell w h)) :
    Push.Scan.eval (Push.Scan.lines side (requests.filter fun a => a.2 ≠ 0)) E =
      Push.Scan.eval (Push.Scan.lines side requests) E := by
  induction requests generalizing E with
  | nil => rfl
  | cons a rest ih =>
    by_cases hz : a.2 = 0
    · simp only [List.filter_cons, hz, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true,
        ite_false, Push.Scan.lines, List.map_cons, Push.Scan.eval, Push.Scan.Instruction.eval,
        Push.Scan.consume, Option.bind_some]
      exact ih E
    · simp only [List.filter_cons, hz, ne_eq, not_false_eq_true, decide_true, ite_true,
        Push.Scan.lines, List.map_cons, Push.Scan.eval]
      apply congrArg ((Push.Scan.Instruction.read side a.1 a.2).eval E).bind
      funext G
      exact ih G

private theorem Exec.restore_zero {side : Direction} (requests : List (ℕ × ℕ))
    {E F : Finset (Cell w h)}
    (H : Exec (Push.Scan.lines side (requests.filter fun a => a.2 ≠ 0)) E F) :
    Exec (Push.Scan.lines side requests) E F := by
  induction requests generalizing E with
  | nil => exact H
  | cons a rest ih =>
    by_cases hz : a.2 = 0
    · simp only [List.filter_cons, hz, ne_eq, not_true_eq_false, decide_false,
        Bool.false_eq_true, ite_false] at H
      apply Exec.cons (F := E) ?_ (ih H)
      exact ⟨by simp only [Push.Scan.Instruction.eval, hz, Push.Scan.consume], by simp⟩
    · simp only [List.filter_cons, hz, ne_eq, not_false_eq_true, decide_true, ite_true] at H
      cases H with
      | cons head tail => exact .cons head (ih tail)

/-- A single whole final cut suffices for every distinct positive sparse lane;
all zero-quota requests are reinserted as empty reads. -/
private theorem Exec.lines_of_eval_positive {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)}
    (hnd : ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup)
    (he : Push.Scan.eval (Push.Scan.lines side requests) E = some F)
    (hwhole : NoSplit side E F) : Exec (Push.Scan.lines side requests) E F := by
  apply Exec.restore_zero requests
  apply Exec.lines_of_eval hnd ?_ hwhole
  rw [eval_drop_zero]
  exact he

/-- After a full-budget argument has removed all overpayment, dense whole reads
recover the emitted sparse word with the same exact terminal bitmap. -/
theorem Exec.denormalize {side : Direction} {requests : List (ℕ × ℕ)}
    {E F : Finset (Cell w h)}
    (H : Exec (Push.Scan.lines side (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h requests))) E F)
    (hbound : ∀ a ∈ requests, a.1 < Push.Scan.laneCount side w h)
    (hnd : ((requests.filter fun a => a.2 ≠ 0).map Prod.fst).Nodup) :
    Exec (Push.Scan.lines side requests) E F := by
  have hloos : LooseExec
      (Push.Scan.lines side (Push.Scan.ofQuotas (Push.Scan.denseQuotas side w h requests))) E F :=
    H.loosen_lines (List.forall₂_same.mpr (by intro a _; exact ⟨rfl, le_rfl⟩))
  apply Exec.lines_of_eval_positive hnd ?_ hloos.lines_no_split
  rw [Push.Scan.eval_normalize side w h requests hbound]
  exact H.eval

end PushPuzzle.PushPush.WholeScan

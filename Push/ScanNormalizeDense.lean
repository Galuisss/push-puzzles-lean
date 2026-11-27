/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalizeCommutation

/-! Adding one literal request to the appropriate lane of a dense parallel scan. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

variable {w h : ℕ}

private def denseFrom (side : Direction) : ℕ → List ℕ → List (Instruction w h)
  | _, [] => []
  | start, q :: quotas => .read side start q :: denseFrom side (start + 1) quotas

private theorem denseFrom_eq (side : Direction) (start : ℕ) (quotas : List ℕ) :
    denseFrom (w := w) (h := h) side start quotas =
      List.ofFn (fun i : Fin quotas.length => Instruction.read side (start + i.val) quotas[i]) := by
  induction quotas generalizing start with
  | nil => rfl
  | cons q quotas ih =>
    rw [List.ofFn_succ]
    simp only [denseFrom, Fin.getElem_fin]
    congr 1
    rw [ih]
    apply congrArg List.ofFn
    funext i
    simp only [Fin.val_succ, List.getElem_cons_succ]
    congr 1
    omega

private theorem denseFrom_zero (side : Direction) (quotas : List ℕ) :
    denseFrom (w := w) (h := h) side 0 quotas = lines side (ofQuotas quotas) := by
  rw [denseFrom_eq]
  simp only [lines, ofQuotas, List.map_ofFn, Nat.zero_add, Function.comp_def, Fin.getElem_fin]

private theorem eval_denseFrom_modify (side : Direction) (quotas : List ℕ)
    (start index q : ℕ) (hindex : index < quotas.length) (E : Finset (Cell w h)) :
    eval (denseFrom side start (quotas.modify index (q + ·))) E =
      ((Instruction.read side (start + index) q).eval E).bind (eval (denseFrom side start quotas)) := by
  induction quotas generalizing start index E with
  | nil => simp only [List.length_nil] at hindex; omega
  | cons a quotas ih =>
    cases index with
    | zero =>
      simp only [List.modify_zero_cons, denseFrom, eval, Nat.add_zero]
      rw [← Option.bind_assoc, read_bind_add]
    | succ index =>
      have hi : index < quotas.length := by simp only [List.length_cons] at hindex; omega
      simp only [List.modify_succ_cons, denseFrom, eval]
      have hidx : start + (index + 1) = (start + 1) + index := by omega
      rw [hidx]
      simp_rw [ih (start + 1) index hi]
      rw [← Option.bind_assoc, read_bind_commute, Option.bind_assoc]

/-- Increasing one dense quota by `q` executes exactly the extra same-direction lane read. -/
theorem eval_dense_modify (side : Direction) (quotas : List ℕ) (lane q : ℕ)
    (hlane : lane < quotas.length) (E : Finset (Cell w h)) :
    eval (lines side (ofQuotas (quotas.modify lane (q + ·)))) E =
      ((Instruction.read side lane q).eval E).bind (eval (lines side (ofQuotas quotas))) := by
  simpa only [denseFrom_zero, Nat.zero_add] using eval_denseFrom_modify side quotas 0 lane q hlane E

end PushPuzzle.Push.Scan

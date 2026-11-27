/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanNormalizeDense
public import Mathlib.Data.List.GetD
import all Push.ScanNormalizeDense

/-! Exact normalization of bounded sparse same-direction requests to one dense quota vector. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- The number of actual lanes perpendicular to the selected reading direction. -/
@[expose] def laneCount (side : Direction) (w h : ℕ) : ℕ :=
  match side with
  | .north | .south => w
  | .east | .west => h

/-- Sum every request naming the specified lane, including repeated entries. -/
@[expose] def quotaAt (requests : List (ℕ × ℕ)) (lane : ℕ) : ℕ :=
  ((requests.filter fun a => a.1 = lane).map Prod.snd).sum

/-- Sum every repeated request on its actual lane, emitting one entry for every board lane. -/
@[expose] def denseQuotas (side : Direction) (w h : ℕ) (requests : List (ℕ × ℕ)) : List ℕ :=
  List.ofFn fun i : Fin (laneCount side w h) => quotaAt requests i.val

@[simp] theorem denseQuotas_length (side : Direction) (w h : ℕ) (requests : List (ℕ × ℕ)) :
    (denseQuotas side w h requests).length = laneCount side w h := List.length_ofFn

private theorem quotaAt_cons (a : ℕ × ℕ) (requests : List (ℕ × ℕ)) (lane : ℕ) :
    quotaAt (a :: requests) lane = (if a.1 = lane then a.2 else 0) + quotaAt requests lane := by
  by_cases h : a.1 = lane <;> simp [quotaAt, h]

private theorem denseQuotas_cons (side : Direction) (w h : ℕ) (a : ℕ × ℕ)
    (requests : List (ℕ × ℕ)) :
    denseQuotas side w h (a :: requests) = (denseQuotas side w h requests).modify a.1 (a.2 + ·) := by
  apply List.ext_getElem
  · simp only [denseQuotas_length, List.length_modify]
  · intro i hi hi'
    simp only [denseQuotas, List.getElem_ofFn, List.getElem_modify, quotaAt_cons]
    by_cases he : a.1 = i
    · simp only [he, ite_true]
    · simp only [he, ite_false, Nat.zero_add]

private theorem eval_denseFrom_zero {w h : ℕ} (side : Direction) (n start : ℕ)
    (E : Finset (Cell w h)) : eval (denseFrom side start (List.replicate n 0)) E = some E := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [List.replicate_succ, denseFrom, eval, Instruction.eval, consume, Option.bind_some, ih]

/-- Sparse requests and their dense per-lane sums have exactly the same complete remainder on all four sides. -/
theorem eval_normalize (side : Direction) (w h : ℕ) (requests : List (ℕ × ℕ))
    (hbounded : ∀ a ∈ requests, a.1 < laneCount side w h) (E : Finset (Cell w h)) :
    eval (lines side requests) E = eval (lines side (ofQuotas (denseQuotas side w h requests))) E := by
  induction requests generalizing E with
  | nil =>
    simp only [denseQuotas, quotaAt, List.filter_nil, List.map_nil, List.sum_nil, List.ofFn_const]
    simpa only [denseFrom_zero, lines, List.map_nil, eval] using (eval_denseFrom_zero side (laneCount side w h) 0 E).symm
  | cons a requests ih =>
    have ha : a.1 < (denseQuotas side w h requests).length := by
      rw [denseQuotas_length]
      exact hbounded a (List.mem_cons_self ..)
    rw [denseQuotas_cons, eval_dense_modify side _ a.1 a.2 ha]
    simp only [lines, List.map_cons, eval]
    apply congrArg ((Instruction.read side a.1 a.2).eval E).bind
    funext F
    exact ih (fun b hb => hbounded b (List.mem_cons_of_mem a hb)) F

private theorem sum_modify_add (quotas : List ℕ) (lane q : ℕ) (hlane : lane < quotas.length) :
    (quotas.modify lane (q + ·)).sum = q + quotas.sum := by
  induction quotas generalizing lane with
  | nil => simp only [List.length_nil] at hlane; omega
  | cons a quotas ih =>
    cases lane with
    | zero => simp only [List.modify_zero_cons, List.sum_cons]; omega
    | succ lane =>
      have hi : lane < quotas.length := by simp only [List.length_cons] at hlane; omega
      rw [List.modify_succ_cons, List.sum_cons, ih lane hi, List.sum_cons]
      omega

/-- Normalization preserves the complete requested quota budget. -/
theorem denseQuotas_sum (side : Direction) (w h : ℕ) (requests : List (ℕ × ℕ))
    (hbounded : ∀ a ∈ requests, a.1 < laneCount side w h) :
    (denseQuotas side w h requests).sum = (requests.map Prod.snd).sum := by
  induction requests with
  | nil => simp [denseQuotas, quotaAt, List.ofFn_const]
  | cons a requests ih =>
    have ha : a.1 < (denseQuotas side w h requests).length := by
      rw [denseQuotas_length]
      exact hbounded a (List.mem_cons_self ..)
    rw [denseQuotas_cons, sum_modify_add _ _ _ ha,
      ih (fun b hb => hbounded b (List.mem_cons_of_mem a hb)), List.map_cons, List.sum_cons]

end PushPuzzle.Push.Scan

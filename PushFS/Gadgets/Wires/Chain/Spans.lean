/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Init
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Exact filling by 40/59-span physical wire tiles

For every `n ≥ 2301`, choose `b = (19*n)%40` and `a = (n-59*b)/40`.
The resulting explicit tile/offset list has exact total span n and a genuine
machine polynomial-time implementation under the unary span encoding.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain.Spans


open Turing.MultiTapeTM ComputableInPolyTime

def longCount (n : ℕ) : ℕ := (19 * n) % 40
def shortCount (n : ℕ) : ℕ := (n - 59 * longCount n) / 40

private theorem longCount_lt (n : ℕ) : longCount n < 40 := Nat.mod_lt _ (by decide)

theorem exact_span (n : ℕ) (hn : 2301 ≤ n) : 40 * shortCount n + 59 * longCount n = n := by
  have hb := longCount_lt n
  have hmod := Nat.mod_add_div (19 * n) 40
  change longCount n + 40 * (19 * n / 40) = 19 * n at hmod
  have hremaining := Nat.mod_add_div (n - 59 * longCount n) 40
  unfold shortCount
  omega

def span (kind : Bool) : ℕ := if kind then 59 else 40

def offset (n i : ℕ) : ℕ := if i < shortCount n then 40 * i else 40 * shortCount n + 59 * (i - shortCount n)
def kindAt (n i : ℕ) : Bool := decide (shortCount n ≤ i)
def patches (n : ℕ) : List (ℕ × Bool) :=
  (List.range (shortCount n + longCount n)).map fun i => (offset n i, kindAt n i)

theorem offset_zero (n : ℕ) : offset n 0 = 0 := by simp [offset]
theorem offset_next (n i : ℕ) : offset n (i+1) = offset n i + span (kindAt n i) := by
  unfold offset span kindAt
  split_ifs <;> simp_all <;> omega

theorem offset_finish (n : ℕ) (hn : 2301 ≤ n) : offset n (shortCount n + longCount n) = n := by
  have hh := exact_span n hn
  unfold offset
  split_ifs <;> omega

theorem offset_le (n i : ℕ) (hn : 2301 ≤ n) (hi : i ≤ shortCount n + longCount n) : offset n i ≤ n := by
  have hh := exact_span n hn
  unfold offset
  split_ifs <;> omega

@[fun_prop] theorem longCount_polyTime : ComputableInPolyTime longCount encUnary encUnary := by
  unfold longCount; fun_prop
@[fun_prop] theorem shortCount_polyTime : ComputableInPolyTime shortCount encUnary encUnary := by
  unfold shortCount; fun_prop
@[fun_prop] theorem offset_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ => offset p.1 p.2)
    (encPair encUnary encUnary) encUnary := by unfold offset; fun_prop
@[fun_prop] theorem kindAt_polyTime : ComputableInPolyTime (fun p : ℕ × ℕ => kindAt p.1 p.2)
    (encPair encUnary encUnary) encBool := by unfold kindAt; fun_prop

end PushPuzzle.PushFS.Gadgets.Wires.Chain.Spans

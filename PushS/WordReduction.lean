/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.WordTopology
public import PushS.WordPhysical
public import PushS.Fallback

/-! The total standard polynomial-time reduction from the original fixed-alphabet word problem. -/

public section
namespace PushPuzzle.PushS.WordSource

open Cslib.Complexity

open _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Compile the original admitted endpoint pair to its actual wall-free board. -/
@[expose] def checkedCompile (x : NCL.HWord.Instance q) : Instance :=
  if guard H hq x then puzzle H hq x (layout_pages_valid H hq x) else Reduction.reject

/-- The complete total compiler is polynomial-time in the standard dense instance encoding. -/
theorem computableInPolyTime_checkedCompile :
    ComputableInPolyTime (checkedCompile H hq) (NCL.HWord.encInstance q) encoding :=
  ComputableInPolyTime.ite (computableInPolyTime_guard H hq)
    (computableInPolyTime_puzzle H hq (layout_pages_valid H hq)) (ComputableInPolyTime.const Reduction.reject)

/-- The original fixed-alphabet word language is exactly solvability of its actual emitted board. -/
theorem checkedCompile_mem_iff (x : NCL.HWord.Instance q) :
    x ∈ NCL.HWord.language H ↔ (checkedCompile H hq x).Solvable := by
  by_cases hx : guard H hq x = true
  · rw [checkedCompile, ite_eq_left hx]
    exact (puzzle_solvable_iff H hq (x := x) hx (layout_pages_valid H hq x)).symm
  · rw [checkedCompile, ite_eq_right hx]
    exact iff_of_false (fun h => hx (guard_of_mem H hq (x := x) h)) Reduction.reject_not_solvable

include hq in
/-- The actual fixed-alphabet compiler is a standard many-one polynomial-time reduction to Push-*S. -/
theorem polyTimeReducible_word :
    PolyTimeReducible (NCL.HWord.encInstance q) encoding (NCL.HWord.language H) solvable :=
  ⟨checkedCompile H hq, computableInPolyTime_checkedCompile H hq, checkedCompile_mem_iff H hq⟩

end PushPuzzle.PushS.WordSource

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourceReader
public import Push.Fallback

/-! The total standard PT ordinary point compiler with the original native endpoint guard. -/

public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Check the original endpoint legality and compile the actual complete source acceptance problem. -/
@[expose] noncomputable def checkedCompile (x : NCL.HWord.Instance q) : Push.Instance :=
  if guard H hq x then pointCompile H hq x else Fallback.reject

/-- The complete guarded physical compiler is standard PT on the original H-word input. -/
theorem computableInPolyTime_checkedCompile : ComputableInPolyTime (checkedCompile H hq)
    (NCL.HWord.encInstance q) Push.encoding :=
  ComputableInPolyTime.ite (computableInPolyTime_guard H hq)
    (computableInPolyTime_pointCompile H hq) (ComputableInPolyTime.const Fallback.reject)

/-- Every actual compiled solution is exactly a guarded, accepted computation of the repaired hard source. -/
theorem checkedCompile_solvable_iff (x : NCL.HWord.Instance q) :
    (checkedCompile H hq x).Solvable ↔ guard H hq x = true ∧ accepted H hq x := by
  by_cases hg : guard H hq x = true
  · rw [checkedCompile, ite_eq_left hg, pointCompile_solvable_iff]
    exact (and_iff_right hg).symm
  · rw [checkedCompile, ite_eq_right hg]
    exact iff_of_false Fallback.reject_not_solvable (fun h => hg h.1)

/-- Every positive original H-word emits a solvable ordinary player-target Push-* instance. -/
theorem checkedCompile_complete {x : NCL.HWord.Instance q} (hx : x ∈ NCL.HWord.language H) :
    (checkedCompile H hq x).Solvable :=
  (checkedCompile_solvable_iff H hq x).mpr
    ⟨PushS.WordSource.guard_of_mem H hq hx, accepted_of_mem H hq hx⟩

end PushPuzzle.Push.WordSource

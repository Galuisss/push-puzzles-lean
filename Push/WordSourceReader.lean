/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordSourcePoint
public import Push.WordSourceProgram
public import Push.AcceptanceProgramFirstQuota
public import Push.AcceptanceProgramReaderFamily

/-! The actual hard source, complete computed acceptance word, and standard PT ordinary point compiler. -/

@[expose] public section
namespace PushPuzzle.Push.WordSource

open PushFS PushS Cslib.Complexity Turing.MultiTapeTM AcceptanceProgram

attribute [local irreducible] PushPuzzle.NCL.HWord.Strip.Sweep.compile
  Partner.Cuts.repair Partner.Cuts.repairAxes

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The actual complete source/program family, with all fixed-skeleton compiler conditions proved. -/
private def readerFamily : CyclicReader.ProgramFamily (NCL.HWord.Instance q)
    (NCL.HWord.encInstance q)
    ((skeleton (levelBudget q + 1)).drop 2) :=
  AcceptanceProgram.readerFamily (layout := layout H hq) (p := scales H hq)
    (initial := initialAxes H hq) (target := targetAxes H hq)
    (layout_valid H hq) (highest_le_scales_levels H hq) (portCount_le_scales_axes H hq)
    (fun _ => rfl) (computableInPolyTime_puzzle H hq) (program_rounds_polyTime H hq)

/-- The emitted ordinary point instance recognizes exactly the actual complete source acceptance computation. -/
theorem exists_pointCompile :
    ∃ compile : NCL.HWord.Instance q → Push.Instance,
      ComputableInPolyTime compile (NCL.HWord.encInstance q) Push.encoding ∧
        ∀ x, (compile x).Solvable ↔ accepted H hq x := by
  obtain ⟨compile, hpt, hcorrect⟩ := (readerFamily H hq).compile
  exact ⟨compile, hpt, hcorrect⟩

/-- Choose the standard PT physical compiler obtained by the fixed finite read/clear recursion. -/
noncomputable def pointCompile : NCL.HWord.Instance q → Push.Instance :=
  Classical.choose (exists_pointCompile H hq)

/-- The complete actual point compiler is standard polynomial time on the original H-word input. -/
theorem computableInPolyTime_pointCompile :
    ComputableInPolyTime (pointCompile H hq) (NCL.HWord.encInstance q) Push.encoding :=
  (Classical.choose_spec (exists_pointCompile H hq)).1

/-- Every successful compiled ordinary point game yields one actual accepted source computation, and conversely. -/
theorem pointCompile_solvable_iff (x : NCL.HWord.Instance q) :
    (pointCompile H hq x).Solvable ↔ accepted H hq x :=
  (Classical.choose_spec (exists_pointCompile H hq)).2 x

end PushPuzzle.Push.WordSource

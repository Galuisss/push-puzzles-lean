/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.WordReduction
public import PushS.UpperBound

/-! Standard PSPACE-completeness of unlimited pushing with all boxes stored and no fixed walls. -/

public section
namespace PushPuzzle.PushS

open Cslib.Complexity

/-- Push-*S is PSPACE-hard under the standard explicit dense instance encoding. -/
theorem solvable_pspaceHard : PSPACEHard encoding solvable := by
  classical
  obtain ⟨q, H, hq, hhard⟩ := NCL.HWord.exists_language_pspaceHard
  exact hhard.trans (WordSource.polyTimeReducible_word H hq)

/-- Push-*S is PSPACE-complete: unlimited pushing, no fixed walls, and all boxes on goals. -/
theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.PushS

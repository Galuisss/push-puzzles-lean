/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.WordReduction
public import Push.UpperBound

/-! Standard PSPACE-completeness of unlimited wall-free pushing with a player-target objective. -/

public section
namespace PushPuzzle.Push

open Cslib.Complexity

/-- Ordinary Push-* is PSPACE-hard under its standard explicit dense instance encoding. -/
theorem solvable_pspaceHard : PSPACEHard encoding solvable := by
  classical
  obtain ⟨q, H, hq, hard⟩ := NCL.HWord.exists_language_pspaceHard
  exact hard.trans (WordSource.polyTimeReducible_word H hq)

/-- Ordinary Push-* is PSPACE-complete: unlimited pushing, no fixed walls, and a designated player target. -/
theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.Push

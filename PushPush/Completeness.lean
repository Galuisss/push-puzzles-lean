/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Compiler
public import PushPush.UpperBound
public import CslibFrontier.Computability.Complexity.Problems.SelfClosingDoor.Completeness

/-! Standard PSPACE-completeness of wall-free unlimited maximum sliding to a player target. -/

public section
namespace PushPuzzle.PushPush

open Cslib.Complexity

theorem solvable_pspaceHard : PSPACEHard encoding solvable :=
  SelfClosingDoor.Reachability_pspaceHard.trans polyTimeReducible_reachability

theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.PushPush

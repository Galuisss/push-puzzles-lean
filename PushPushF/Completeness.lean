/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushF.UpperBound
public import PushPushF.WallFree
public import PushPush.Completeness

/-! PSPACE-completeness of fixed-wall unlimited maximum sliding to a player target. -/

public section
namespace PushPuzzle.PushPushF

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- Empty-wall inclusion preserves the dense encoding and the player target. -/
theorem polyTimeReducible_wallFree :
    PolyTimeReducible PushPush.encoding encoding PushPush.solvable solvable :=
  ⟨ofWallFree, of_eq fun _ => rfl, fun I => (solvable_wallFree_iff I).symm⟩

theorem solvable_pspaceHard : PSPACEHard encoding solvable :=
  PushPush.solvable_pspaceHard.trans polyTimeReducible_wallFree

/-- PushPush-*F is PSPACE-complete. -/
theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.PushPushF

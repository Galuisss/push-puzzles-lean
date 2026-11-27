/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.UnlimitedUpperBound
public import PushPushS.Completeness

/-! PSPACE-completeness of exact storage with walls and unrestricted maximum sliding. -/

public section
namespace PushPuzzle.PushPushFS.Unlimited

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- Adding an empty wall set preserves the dense input and every storage solution. -/
theorem polyTimeReducible_wallFree :
    PolyTimeReducible PushPushS.encoding encoding PushPushS.solvable solvable :=
  ⟨PushS.Instance.toInstance, of_eq fun _ => rfl,
    fun I => (solvable_wallFree_iff I).symm⟩

theorem solvable_pspaceHard : PSPACEHard encoding solvable :=
  PushPushS.solvable_pspaceHard.trans polyTimeReducible_wallFree

/-- PushPush-*FS is PSPACE-complete. -/
theorem solvable_pspaceComplete : PSPACEComplete encoding solvable :=
  ⟨solvable_mem_PSPACE, solvable_pspaceHard⟩

end PushPuzzle.PushPushFS.Unlimited

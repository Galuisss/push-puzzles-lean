/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.UpperBound
public import PushPushFS.WallFree
public import PushPushS.FiniteCompleteness

/-! PSPACE-completeness of exact storage with walls and a fixed positive sliding push limit. -/

public section
namespace PushPuzzle.PushPushFS

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

/-- Viewing a wall-free board as a board with walls preserves its dense encoding and solutions. -/
theorem polyTimeReducible_wallFree (k : ℕ) :
    PolyTimeReducible PushPushS.encoding encoding (PushPushS.solvableFinite k) (solvable k) :=
  ⟨PushS.Instance.toInstance, of_eq fun _ => rfl,
    fun I => (solvable_wallFree_iff I k).symm⟩

theorem solvable_finite_pspaceHard (k : ℕ) (hk : 1 ≤ k) :
    PSPACEHard encoding (solvable k) :=
  (PushPushS.solvable_finite_pspaceHard k hk).trans (polyTimeReducible_wallFree k)

/-- PushPush-kFS is PSPACE-complete for every fixed k ≥ 1. -/
theorem solvable_finite_pspaceComplete (k : ℕ) (hk : 1 ≤ k) :
    PSPACEComplete encoding (solvable k) :=
  ⟨solvable_mem_PSPACE k, solvable_finite_pspaceHard k hk⟩

/-- PushPush-1FS is PSPACE-complete. -/
theorem solvable_one_pspaceComplete : PSPACEComplete encoding (solvable 1) :=
  solvable_finite_pspaceComplete 1 le_rfl

end PushPuzzle.PushPushFS

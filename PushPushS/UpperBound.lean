/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Space.Goal
public import PushPush.Space.SearchGraph

/-! Unlimited-strength maximum sliding with exact storage belongs to PSPACE. -/

public section
namespace PushPuzzle.PushPushS

open Cslib.Complexity

/-- PushPush-*S is in PSPACE for explicitly represented wall-free storage boards. -/
theorem solvable_mem_PSPACE : solvable ∈ PSPACE encoding := by
  have h := PushPush.SearchGraph.language_mem_PSPACE PushS.Instance.toInstance Machine.goal
    PushS.toInstance_polyTime Machine.goal_polyTime
  have he : PushPush.SearchGraph.Language PushS.Instance.toInstance Machine.goal = solvable :=
    Set.ext fun I => Machine.goal_exists_iff I (PushPush.Reachable I.initial)
      fun _ hr => hr.valid I.initial_valid.2.2
  rwa [he] at h

end PushPuzzle.PushPushS

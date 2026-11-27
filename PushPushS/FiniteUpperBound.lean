/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.FiniteBasic
public import PushPushS.Space.Goal
public import PushPush.Space.FiniteSearchGraph

/-! Finite-strength maximum sliding with exact storage belongs to PSPACE. -/

public section
namespace PushPuzzle.PushPushS

variable (limit : ℕ)

open Cslib.Complexity

/-- PushPush-kS is in PSPACE for explicitly represented wall-free storage boards. -/
theorem solvableFinite_mem_PSPACE : solvableFinite limit ∈ PSPACE encoding := by
  have h := PushPush.Finite.SearchGraph.language_mem_PSPACE limit PushS.Instance.toInstance Machine.goal
    PushS.toInstance_polyTime Machine.goal_polyTime
  have he : PushPush.Finite.SearchGraph.Language limit PushS.Instance.toInstance Machine.goal = solvableFinite limit :=
    Set.ext fun I => Machine.goal_exists_iff I (PushPush.Finite.Reachable limit I.initial)
      fun _ hr => hr.valid I.initial_valid.2.2
  rwa [he] at h

end PushPuzzle.PushPushS

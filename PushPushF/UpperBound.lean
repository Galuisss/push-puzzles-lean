/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushF.Space.Goal
public import PushPushFS.UnlimitedEdge
public import PushPush.Space.DecisionSearch

/-! Fixed-wall unlimited maximum sliding to a player target belongs to PSPACE. -/

public section
namespace PushPuzzle.PushPushF

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

private def system : PushPush.DecisionSearch.System Instance.toStorage where
  step I := PushPushFS.Unlimited.Step I.board
  edge q := PushPushFS.Unlimited.Machine.edge (q.1.toStorage, q.2)
  correct I u v := PushPushFS.Unlimited.Machine.edge_correct I.toStorage u v

private theorem edge_polyTime :
    ComputableInPolyTime system.edge (encPair encoding (encPair encBits encBits)) encBool := by
  change ComputableInPolyTime
    (fun q : Instance × List Bool × List Bool =>
      PushPushFS.Unlimited.Machine.edge (q.1.toStorage, q.2))
    (encPair encoding (encPair encBits encBits)) encBool
  fun_prop

private theorem terminal_language_iff (I : Instance) :
    I ∈ PushPush.DecisionSearch.Language Instance.toStorage Machine.goal system ↔
      Instance.Solvable I := by
  constructor
  · rintro ⟨s, hr, hg⟩
    exact ⟨s, hr, ((Machine.goal_state_correct I s).mp hg).2⟩
  · rintro ⟨s, hr, hs⟩
    exact ⟨s, hr, (Machine.goal_state_correct I s).mpr
      ⟨hr.valid I.initial_valid, hs⟩⟩

/-- PushPush-*F is in PSPACE under the explicit dense board encoding. -/
theorem solvable_mem_PSPACE : solvable ∈ PSPACE encoding := by
  have h := PushPush.DecisionSearch.language_mem_PSPACE Instance.toStorage Machine.goal system
    Machine.toStorage_polyTime Machine.goal_polyTime edge_polyTime
  have he : PushPush.DecisionSearch.Language Instance.toStorage Machine.goal system =
      solvable := Set.ext terminal_language_iff
  rwa [he] at h

end PushPuzzle.PushPushF

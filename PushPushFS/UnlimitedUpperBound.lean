/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.UnlimitedEdge
public import PushPush.Space.DecisionSearch
public import PushFS.Space.Goal

/-! Fixed-wall maximum sliding with unrestricted push strength belongs to PSPACE. -/

public section
namespace PushPuzzle.PushPushFS.Unlimited

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

private def system : PushPush.DecisionSearch.System (id : Instance → Instance) where
  step I := Step I.board
  edge := Machine.edge
  correct := Machine.edge_correct

private theorem terminal_language_iff (I : Instance) :
    I ∈ PushPush.DecisionSearch.Language id PushFS.Machine.goal system ↔ Solvable I := by
  constructor
  · rintro ⟨s, hr, hg⟩
    exact ⟨s, hr, ((PushFS.Machine.goal_state_correct I s).mp hg).2⟩
  · rintro ⟨s, hr, hs⟩
    exact ⟨s, hr, (PushFS.Machine.goal_state_correct I s).mpr
      ⟨hr.valid I.initial_valid, hs⟩⟩

/-- PushPush-*FS belongs to PSPACE under the explicit dense board encoding. -/
theorem solvable_mem_PSPACE : solvable ∈ PSPACE encoding := by
  have h := PushPush.DecisionSearch.language_mem_PSPACE id PushFS.Machine.goal system
    (by fun_prop) PushFS.Machine.goal_polyTime Machine.edge_polyTime
  have he : PushPush.DecisionSearch.Language id PushFS.Machine.goal system = solvable :=
    Set.ext terminal_language_iff
  rwa [he] at h

end PushPuzzle.PushPushFS.Unlimited

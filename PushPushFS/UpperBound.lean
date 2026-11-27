/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Space.Edge
public import PushPush.Space.DecisionSearch
public import PushFS.Space.Goal

/-! Fixed-wall maximum sliding at every fixed push limit belongs to PSPACE. -/

public section
namespace PushPuzzle.PushPushFS

open Cslib.Complexity Turing.MultiTapeTM ComputableInPolyTime

private def system (limit : ℕ) : PushPush.DecisionSearch.System (id : Instance → Instance) where
  step I := Step I.board limit
  edge := Machine.edge limit
  correct := Machine.edge_correct limit

private theorem terminal_language_iff (limit : ℕ) (I : Instance) :
    I ∈ PushPush.DecisionSearch.Language id PushFS.Machine.goal (system limit) ↔
      Instance.Solvable I limit := by
  constructor
  · rintro ⟨s, hr, hg⟩
    exact ⟨s, hr, ((PushFS.Machine.goal_state_correct I s).mp hg).2⟩
  · rintro ⟨s, hr, hs⟩
    exact ⟨s, hr, (PushFS.Machine.goal_state_correct I s).mpr
      ⟨hr.valid I.initial_valid, hs⟩⟩

/-- PushPush-kFS is in PSPACE for every fixed finite push limit. -/
theorem solvable_mem_PSPACE (limit : ℕ) : solvable limit ∈ PSPACE encoding := by
  have h := PushPush.DecisionSearch.language_mem_PSPACE id PushFS.Machine.goal (system limit)
    (by fun_prop) PushFS.Machine.goal_polyTime (Machine.edge_polyTime limit)
  have he : PushPush.DecisionSearch.Language id PushFS.Machine.goal (system limit) =
      solvable limit := Set.ext (terminal_language_iff limit)
  rwa [he] at h

end PushPuzzle.PushPushFS

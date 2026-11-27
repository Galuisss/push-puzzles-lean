/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Basic
public import PushPush.Space.SearchGraph
public import Push.Space.Goal

/-! Maximum-slide player reachability belongs to PSPACE under the dense board encoding. -/

public section
namespace PushPuzzle.PushPush

open Cslib.Complexity

private theorem terminal_language_iff (I : Instance) :
    I ∈ SearchGraph.Language Push.Instance.toStorage Push.Machine.goal ↔
      Instance.Solvable I := by
  constructor
  · rintro ⟨s, hr, hg⟩
    exact ⟨s, hr, ((Push.Machine.goal_state_correct I s).mp hg).2⟩
  · rintro ⟨s, hr, hs⟩
    refine ⟨s, hr, (Push.Machine.goal_state_correct I s).mpr ⟨?_, hs⟩⟩
    exact ⟨by simp, by simp, hr.valid I.player_empty⟩

/-- PushPush-* is in PSPACE for explicitly represented wall-free rectangles. -/
theorem solvable_mem_PSPACE : solvable ∈ PSPACE encoding := by
  have h := SearchGraph.language_mem_PSPACE Push.Instance.toStorage Push.Machine.goal
    Push.Machine.toStorage_polyTime Push.Machine.goal_polyTime
  have he : SearchGraph.Language Push.Instance.toStorage Push.Machine.goal = solvable :=
    Set.ext terminal_language_iff
  rwa [he] at h

end PushPuzzle.PushPush

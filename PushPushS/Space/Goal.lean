/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Basic
public import PushS.UpperBound
public import PushFS.Space.Goal

/-! The common exact-storage terminal test for wall-free maximum sliding. -/

public section
namespace PushPuzzle.PushPushS.Machine

open Turing.MultiTapeTM ComputableInPolyTime

/-- A well-formed solved state under the common dense storage encoding. -/
def goal (q : Instance × List Bool) : Bool :=
  PushFS.Machine.goal (q.1.toInstance, q.2)

@[fun_prop] theorem goal_polyTime :
    ComputableInPolyTime goal (encPair encoding encBits) encBool := by
  unfold goal
  fun_prop

/-- On player-valid states, the terminal test is exactly the required box-set equality. -/
theorem goal_exists_iff (I : Instance) (P : PushFS.State I.width I.height → Prop)
    (hvalid : ∀ s, P s → s.player ∉ s.boxes) :
    (∃ s, P s ∧ goal (I, s.bits) = true) ↔ ∃ s, P s ∧ s.boxes = I.board.goals := by
  constructor
  · rintro ⟨s, hs, hg⟩
    exact ⟨s, hs, ((PushFS.Machine.goal_state_correct I.toInstance s).mp hg).2⟩
  · rintro ⟨s, hs, hg⟩
    refine ⟨s, hs, (PushFS.Machine.goal_state_correct I.toInstance s).mpr ⟨?_, hg⟩⟩
    exact ⟨by simp [I.walls_empty], by simp [I.walls_empty], hvalid s hs⟩

end PushPuzzle.PushPushS.Machine

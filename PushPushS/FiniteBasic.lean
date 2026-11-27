/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Basic
public import PushPush.Finite

/-! Exact storage with a fixed bound on maximum-slide run lengths. -/

@[expose] public section
namespace PushPuzzle.PushPushS

/-- Every box reaches its target with at most `limit` boxes starting each slide. -/
def Instance.SolvableFinite (I : Instance) (limit : ℕ) : Prop :=
  ∃ t, PushPush.Finite.Reachable limit I.initial t ∧ t.boxes = I.board.goals

/-- The wall-free PushPush-kS decision problem. -/
def solvableFinite (limit : ℕ) : Set Instance := {I | I.SolvableFinite limit}

/-- Removing the push limit preserves exact-storage solutions. -/
theorem Instance.SolvableFinite.unlimited {I : Instance} {limit : ℕ}
    (hs : I.SolvableFinite limit) : I.Solvable := by
  obtain ⟨t, hr, hg⟩ := hs
  exact ⟨t, hr.unlimited, hg⟩

end PushPuzzle.PushPushS

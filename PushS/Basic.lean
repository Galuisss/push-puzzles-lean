/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! Unlimited pushing and exact storage on a finite rectangle with no fixed walls. -/

@[expose] public section
namespace PushPuzzle.PushS


/-- An explicit storage instance whose entire rectangle is floor. -/
structure Instance extends PushFS.Instance where
  /-- There are no fixed internal walls. -/
  walls_empty : board.walls = ∅

theorem Instance.toInstance_injective : Function.Injective Instance.toInstance := by
  rintro ⟨I, hI⟩ ⟨J, hJ⟩ h
  cases h
  rfl

/-- Build a wall-free instance from its goals and initial unlabelled box state. -/
def Instance.ofState {w h : ℕ} (goals : Finset (PushFS.Cell w h))
    (initial : PushFS.State w h) (player_empty : initial.player ∉ initial.boxes)
    (boxes_eq_goals : initial.boxes.card = goals.card) : Instance where
  width := w
  height := h
  board := ⟨∅, goals⟩
  initial := initial
  goals_floor := Finset.disjoint_empty_left _
  initial_valid := ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, player_empty⟩
  boxes_eq_goals := boxes_eq_goals
  walls_empty := rfl

/-- Reach exactly the target box set with unlimited pushing and arbitrary final player. -/
def Instance.Solvable (I : Instance) : Prop := I.toInstance.Solvable none

/-- The wall-free unlimited storage language. -/
def solvable : Set Instance := {I | I.Solvable}

end PushPuzzle.PushS

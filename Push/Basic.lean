/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushFS.Run

/-! Unlimited pushing on a wall-free rectangle with a player destination. -/

@[expose] public section
namespace PushPuzzle.Push

open PushFS

/-- A wall-free instance with ordinary boxes and a designated player destination. -/
structure Instance where
  /-- Rectangle width. -/
  width : ℕ
  /-- Rectangle height. -/
  height : ℕ
  /-- Starting player position and unlabelled boxes. -/
  initial : State width height
  /-- Required final player position. -/
  target : Cell width height
  /-- The player starts on an empty cell. -/
  player_empty : initial.player ∉ initial.boxes

/-- The common game instance used by the step checker. -/
def Instance.toStorage (I : Instance) : PushFS.Instance where
  width := I.width
  height := I.height
  board := ⟨∅, I.initial.boxes⟩
  initial := I.initial
  goals_floor := Finset.disjoint_empty_left _
  initial_valid := ⟨Finset.notMem_empty _, Finset.disjoint_empty_right _, I.player_empty⟩
  boxes_eq_goals := rfl

/-- The wall-free board for the common pushing semantics. -/
abbrev Instance.board (I : Instance) : Board I.width I.height := I.toStorage.board

/-- Reach the target player cell; all final box positions are allowed. -/
def Instance.Solvable (I : Instance) : Prop :=
  ∃ t, Reachable I.board none I.initial t ∧ t.player = I.target

/-- The ordinary wall-free Push-* language. -/
def solvable : Set Instance := {I | I.Solvable}

theorem Instance.initial_valid (I : Instance) : I.initial.Valid I.board :=
  I.toStorage.initial_valid

@[simp] theorem Instance.walls_empty (I : Instance) : I.board.walls = ∅ := rfl

end PushPuzzle.Push

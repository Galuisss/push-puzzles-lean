/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Unlimited

/-! Maximum sliding with fixed walls and a prescribed player destination. -/

@[expose] public section
namespace PushPuzzle.PushPushF

open PushFS (Cell State Board)

/-- A finite rectangle with fixed walls, ordinary boxes and a player destination. -/
structure Instance where
  /-- Rectangle width. -/
  width : ℕ
  /-- Rectangle height. -/
  height : ℕ
  /-- Fixed inaccessible cells. -/
  walls : Finset (Cell width height)
  /-- Starting player position and unlabelled boxes. -/
  initial : State width height
  /-- Required final player position. -/
  target : Cell width height
  /-- The starting state lies on floor with an empty player cell. -/
  initial_valid : initial.Valid ⟨walls, initial.boxes⟩
  /-- The destination lies on floor. -/
  target_floor : target ∉ walls

/-- The common dense board representation used by the state checker. -/
def Instance.toStorage (I : Instance) : PushFS.Instance where
  width := I.width
  height := I.height
  board := ⟨I.walls, I.initial.boxes⟩
  initial := I.initial
  goals_floor := I.initial_valid.2.1.symm
  initial_valid := I.initial_valid
  boxes_eq_goals := rfl

/-- The board carrying the immutable walls. -/
abbrev Instance.board (I : Instance) : Board I.width I.height := I.toStorage.board

/-- Reach the destination by unlimited maximum slides. -/
def Instance.Solvable (I : Instance) : Prop :=
  ∃ t, PushPushFS.Unlimited.Reachable I.board I.initial t ∧ t.player = I.target

/-- The PushPush-*F decision problem. -/
def solvable : Set Instance := {I | I.Solvable}

end PushPuzzle.PushPushF

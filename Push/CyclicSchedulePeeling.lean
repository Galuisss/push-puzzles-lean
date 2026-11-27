/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicSchedule
public import Push.CyclicTurnProgram

/-! Fixed-shape direction alignment and the decreasing potential of ordinary and erase peeling. -/

public section
namespace PushPuzzle.Push.CyclicSchedule

open PushFS AcceptanceProgram

/-- Apply the actual physical quarter turn to every fixed side tag. -/
@[expose] def turnShapes (shapes : List (Bool × Direction)) : List (Bool × Direction) :=
  shapes.map fun s => (s.1, Cyclic.turnSide s.2)

/-- The suffix after the current west read becomes the new suffix after ordinary peeling. -/
@[expose] def normalSuffix (suffix : List (Bool × Direction)) : List (Bool × Direction) :=
  turnShapes (suffix.drop 1)

/-- Five literal read blocks complete the six-round replacement after the new independent south read. -/
@[expose] def eraseSuffix (tail : List (Bool × Direction)) : List (Bool × Direction) :=
  [(true, .west), (true, .north), (true, .east), (true, .south), (true, .west)] ++ turnShapes tail

/-- Number of actual clear blocks in the fixed shape. -/
@[expose] def clears : List (Bool × Direction) → ℕ
  | [] => 0
  | shape :: rest => (if shape.1 then 0 else 1) + clears rest

/-- Every ordinary peel or erase replacement spends exactly one unit of this syntax potential. -/
@[expose] def potential (shapes : List (Bool × Direction)) : ℕ := shapes.length + 4 * clears shapes

private theorem turn_nextSide (side : Direction) :
    Cyclic.turnSide (nextSide side) = nextSide (Cyclic.turnSide side) := by cases side <;> rfl

@[simp] theorem turnShapes_length (shapes : List (Bool × Direction)) :
    (turnShapes shapes).length = shapes.length := List.length_map _

@[simp] theorem clears_turnShapes (shapes : List (Bool × Direction)) :
    clears (turnShapes shapes) = clears shapes := by
  induction shapes with
  | nil => rfl
  | cons shape shapes ih => simp only [turnShapes, List.map_cons, clears] at ih ⊢; rw [ih]

@[simp] theorem potential_turnShapes (shapes : List (Bool × Direction)) :
    potential (turnShapes shapes) = potential shapes := by simp only [potential, turnShapes_length, clears_turnShapes]

/-- Turning all side tags retains cyclic alignment, with the expected first side turned as well. -/
private theorem turnShapes_aligned (side : Direction) (shapes : List (Bool × Direction))
    (ha : Aligned side shapes) : Aligned (Cyclic.turnSide side) (turnShapes shapes) := by
  induction shapes generalizing side with
  | nil => trivial
  | cons shape shapes ih =>
    obtain ⟨hs, hr⟩ := ha
    refine ⟨congrArg Cyclic.turnSide hs, ?_⟩
    change Aligned (nextSide (Cyclic.turnSide side)) (turnShapes shapes)
    have ht := ih (nextSide side) hr
    simpa only [turn_nextSide] using ht

/-- Removing the current west read and turning the remaining suffix again starts at west. -/
theorem normalSuffix_aligned (tail : List (Bool × Direction))
    (ha : Aligned .west ((true, .west) :: tail)) :
    Aligned .west (normalSuffix ((true, .west) :: tail)) :=
  turnShapes_aligned .north tail ha.2

/-- Ordinary peeling deletes exactly its current read block from the fixed-shape potential. -/
private theorem normalSuffix_potential (side : Direction) (tail : List (Bool × Direction)) :
    potential (normalSuffix ((true, side) :: tail)) + 1 = potential ((true, side) :: tail) := by
  change potential (turnShapes tail) + 1 = potential ((true, side) :: tail)
  rw [potential_turnShapes]
  simp [potential, clears]
  omega

theorem normalSuffix_decreases (side : Direction) (tail : List (Bool × Direction)) :
    potential (normalSuffix ((true, side) :: tail)) < potential ((true, side) :: tail) := by
  have h := normalSuffix_potential side tail
  omega

/-- The backed erase replacement's five suffix reads align with the turned original tail. -/
theorem eraseSuffix_aligned (tail : List (Bool × Direction))
    (ha : Aligned .west ((true, .west) :: (false, .north) :: tail)) :
    Aligned .west (eraseSuffix tail) := by
  have ht := turnShapes_aligned .east tail ha.2.2
  simpa only [eraseSuffix, List.cons_append, List.nil_append, Aligned, nextSide, Cyclic.turnSide, true_and] using ht

/-- Erasure replaces three whole rounds by six and deletes one clear: its potential falls by one. -/
private theorem eraseSuffix_potential (tail : List (Bool × Direction)) :
    potential (eraseSuffix tail) + 1 = potential ((true, .west) :: (false, .north) :: tail) := by
  simp [eraseSuffix, potential, clears]
  omega

theorem eraseSuffix_decreases (tail : List (Bool × Direction)) :
    potential (eraseSuffix tail) < potential ((true, .west) :: (false, .north) :: tail) := by
  have h := eraseSuffix_potential tail
  omega

end PushPuzzle.Push.CyclicSchedule

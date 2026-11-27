/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramSkeleton
public import Push.ScanComposition

/-! Empty read rounds align the actual compact program with the cyclic four-side schedule. -/

public section
namespace PushPuzzle.Push.CyclicSchedule

open PushFS AcceptanceProgram

/-- The next boundary in the physical read order south, west, north, east. -/
@[expose] def nextSide : Direction → Direction
  | .south => .west
  | .west => .north
  | .north => .east
  | .east => .south

/-- Read/clear tags follow the stated cyclic side order. -/
@[expose] def Aligned (side : Direction) : List (Bool × Direction) → Prop
  | [] => True
  | shape :: rest => shape.2 = side ∧ Aligned (nextSide side) rest

/-- Insert at most three literally empty reads before the next requested side. -/
@[expose] def padding (side target : Direction) : List Round :=
  if side = target then []
  else if nextSide side = target then [.read side []]
  else if nextSide (nextSide side) = target then [.read side [], .read (nextSide side) []]
  else [.read side [], .read (nextSide side) [], .read (nextSide (nextSide side)) []]

/-- The complete padding recipe depends only on the two physical side tags. -/
@[expose] def paddingShapes (side target : Direction) : List (Bool × Direction) :=
  (padding side target).map Round.shape

private theorem padding_aligned (side : Direction) (shape : Bool × Direction)
    (rest : List (Bool × Direction)) (hr : Aligned (nextSide shape.2) rest) :
    Aligned side (paddingShapes side shape.2 ++ shape :: rest) := by
  rcases shape with ⟨tag, target⟩
  cases side <;> cases target <;> simpa [paddingShapes, padding, Round.shape, Aligned, nextSide] using hr

private theorem padding_instructions {w h : ℕ} (side target : Direction) :
    instructions (w := w) (h := h) (padding side target) = [] := by
  cases side <;> cases target <;> rfl

/-- Align an actual compact program, preserving every original read or clear block. -/
@[expose] def padFrom : Direction → List Round → List Round
  | _, [] => []
  | side, round :: rest =>
      padding side round.shape.2 ++ round :: padFrom (nextSide round.shape.2) rest

/-- Compute the aligned shape using only the original shape list. -/
@[expose] def padShapesFrom : Direction → List (Bool × Direction) → List (Bool × Direction)
  | _, [] => []
  | side, shape :: rest =>
      paddingShapes side shape.2 ++ shape :: padShapesFrom (nextSide shape.2) rest

theorem padFrom_shapes (side : Direction) (rounds : List Round) :
    (padFrom side rounds).map Round.shape = padShapesFrom side (rounds.map Round.shape) := by
  induction rounds generalizing side with
  | nil => rfl
  | cons round rounds ih => simp only [padFrom, List.map_append, List.map_cons, ih, padShapesFrom, paddingShapes]

theorem padShapesFrom_aligned (side : Direction) (shapes : List (Bool × Direction)) :
    Aligned side (padShapesFrom side shapes) := by
  induction shapes generalizing side with
  | nil => trivial
  | cons shape shapes ih => exact padding_aligned side shape _ (ih _)

private theorem instructions_append {w h : ℕ} (a b : List Round) :
    instructions (w := w) (h := h) (a ++ b) = instructions a ++ instructions b := List.flatMap_append

/-- Empty padding leaves the expanded literal instruction list itself unchanged. -/
theorem padFrom_instructions {w h : ℕ} (side : Direction) (rounds : List Round) :
    instructions (w := w) (h := h) (padFrom side rounds) = instructions rounds := by
  induction rounds generalizing side with
  | nil => rfl
  | cons round rounds ih =>
    rw [padFrom, instructions_append, padding_instructions, List.nil_append]
    change round.instructions ++ instructions (padFrom _ rounds) = round.instructions ++ instructions rounds
    rw [ih]

end PushPuzzle.Push.CyclicSchedule

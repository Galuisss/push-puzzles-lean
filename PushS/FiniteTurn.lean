/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteTools
public import PushS.FiniteWireFrame
import Mathlib.Tactic.FinCases

/-! The thick concave turn, including its two real neighboring boxes. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteTools

open PushFS FiniteGeometry

def turnRectangle (w : ℕ) (i : Fin 2) : Rectangle :=
  if i = 0 then ⟨0, radius w-w, radius w+w+1, w⟩
  else ⟨radius w+1, radius w-w, w, radius w+w+1⟩

def turnWalls (w : ℕ) : Finset (Cell (side w) (side w)) :=
  Finset.univ.biUnion fun i => (turnRectangle w i).cells (side w) (side w)

theorem turnRectangle_thick (w : ℕ) (i : Fin 2) :
    w ≤ (turnRectangle w i).width ∧ w ≤ (turnRectangle w i).height := by
  fin_cases i <;> simp [turnRectangle, radius] <;> omega

/-- The actual turn macros use only the five-by-five exposed quadrant. -/
def turnActive (w : ℕ) : Finset (Cell (side w) (side w)) :=
  (Rectangle.mk (radius w-4) (radius w) 5 5).cells (side w) (side w)

def turnMacroBoard (w : ℕ) : Board (side w) (side w) :=
  FiniteWireFrame.board (turnActive w) ∅

inductive TurnLabel
  | predecessor | horizontal | vertical | successor
  deriving DecidableEq

instance : Fintype TurnLabel where
  elems := {.predecessor, .horizontal, .vertical, .successor}
  complete l := by cases l <;> simp

def turnMixedPoint (w : ℕ) (a b : Bool) : TurnLabel → ℕ × ℕ
  | .predecessor => (radius w-4, radius w)
  | .horizontal => (radius w-2+a.toNat, radius w)
  | .vertical => (radius w, radius w+1+b.toNat)
  | .successor => (radius w, radius w+4)

theorem turnMixedPoint_interior (w : ℕ) (a b : Bool) (l : TurnLabel) :
    (turnMixedPoint w a b l).1 < side w ∧ (turnMixedPoint w a b l).2 < side w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  cases l <;> dsimp [turnMixedPoint, radius, side] <;> omega

def turnMixedCell (w : ℕ) (a b : Bool) (l : TurnLabel) : Cell (side w) (side w) :=
  (⟨(turnMixedPoint w a b l).1, (turnMixedPoint_interior w a b l).1⟩,
   ⟨(turnMixedPoint w a b l).2, (turnMixedPoint_interior w a b l).2⟩)

def turnMixedBoxes (w : ℕ) (a b : Bool) : Finset (Cell (side w) (side w)) :=
  Finset.univ.image (turnMixedCell w a b)

def turnBoxes (w : ℕ) (q : Bool) := turnMixedBoxes w q q

theorem turnMixedCell_injective (w : ℕ) (a b : Bool) :
    Function.Injective (turnMixedCell w a b) := by
  intro i j he
  have hx := congrArg (fun p : Cell (side w) (side w) => p.1.val) he
  have hy := congrArg (fun p : Cell (side w) (side w) => p.2.val) he
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  cases i <;> cases j <;>
    dsimp [turnMixedCell, turnMixedPoint, radius] at hx hy <;> first | rfl | omega

theorem turnMixedCell_active (w : ℕ) (a b : Bool) (l : TurnLabel) :
    turnMixedCell w a b l ∈ turnActive w := by
  have ha := Bool.toNat_le a
  have hb := Bool.toNat_le b
  rw [turnActive, Rectangle.mem_cells]
  cases l <;> dsimp [turnMixedCell, turnMixedPoint, radius] <;> omega

theorem turnMixedBoxes_floor (w : ℕ) (a b : Bool) :
    Disjoint (turnMixedBoxes w a b) (turnMacroBoard w).walls := by
  apply Finset.disjoint_left.mpr
  intro p hp
  obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp hp
  exact (FiniteWireFrame.floor_iff _ _ _).mpr (turnMixedCell_active w a b l)

theorem turnActive_floor (w : ℕ) {p : Cell (side w) (side w)} (hp : p ∈ turnActive w) :
    p ∉ turnWalls w := by
  have hp' := (Rectangle.mem_cells _ _ _ _).mp hp
  intro hw
  obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hw
  have hi' := ((turnRectangle w i).mem_cells _ _ _).mp hi
  fin_cases i <;> simp [turnRectangle, radius] at hi' <;> dsimp [radius] at hp' <;> omega

inductive TurnNode
  | corner | horizontalSupport | horizontal0 | horizontal1 | vertical0 | vertical1
  | horizontalOuter | verticalOuter | verticalSupport
  deriving DecidableEq

def turnNodePoint (w : ℕ) : TurnNode → ℕ × ℕ
  | .corner => (radius w, radius w)
  | .horizontalSupport => (radius w-3, radius w)
  | .horizontal0 => (radius w-2, radius w)
  | .horizontal1 => (radius w-1, radius w)
  | .vertical0 => (radius w, radius w+1)
  | .vertical1 => (radius w, radius w+2)
  | .horizontalOuter => (radius w-3, radius w+1)
  | .verticalOuter => (radius w-1, radius w+3)
  | .verticalSupport => (radius w, radius w+3)

theorem turnNodePoint_interior (w : ℕ) (i : TurnNode) :
    (turnNodePoint w i).1 < side w ∧ (turnNodePoint w i).2 < side w := by
  cases i <;> dsimp [turnNodePoint, radius, side] <;> omega

def turnNode (w : ℕ) (i : TurnNode) : Cell (side w) (side w) :=
  (⟨(turnNodePoint w i).1, (turnNodePoint_interior w i).1⟩,
   ⟨(turnNodePoint w i).2, (turnNodePoint_interior w i).2⟩)

theorem turnNode_active (w : ℕ) (i : TurnNode) : turnNode w i ∈ turnActive w := by
  rw [turnActive, Rectangle.mem_cells]
  cases i <;> dsimp [turnNode, turnNodePoint, radius] <;> omega

end PushPuzzle.PushS.FiniteTools

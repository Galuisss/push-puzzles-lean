/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Init
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Int.Basic
import Lean.Elab.Tactic.Omega

/-!
# A finite rectangular grid

Coordinates start at the top left; `x` increases to the right and `y` downwards.
Adjacency is expressed using natural-number coordinates, never modular arithmetic
on `Fin`. In particular, a move cannot wrap around a boundary.
-/

@[expose] public section

namespace PushPuzzle.PushFS


/-- A cell of a rectangle of width `w` and height `h`. -/
abbrev Cell (w h : ℕ) := Fin w × Fin h

/-- The four directions in which the player can walk or push. -/
inductive Direction
  | north | east | south | west
  deriving DecidableEq, Repr

instance : Fintype Direction where
  elems := {.north, .east, .south, .west}
  complete d := by cases d <;> simp

namespace Direction

/-- Reversing a direction. This does not assert that a push can be reversed. -/
def opposite : Direction → Direction
  | north => south
  | east => west
  | south => north
  | west => east

@[simp] theorem opposite_opposite (d : Direction) : d.opposite.opposite = d := by
  cases d <;> rfl

end Direction

variable {w h : ℕ}

/-- `q` is one unit from `p` in direction `d`, within the rectangle. -/
def Adjacent (d : Direction) (p q : Cell w h) : Prop :=
  match d with
  | .north => q.1 = p.1 ∧ q.2.val + 1 = p.2.val
  | .east => q.1.val = p.1.val + 1 ∧ q.2 = p.2
  | .south => q.1 = p.1 ∧ q.2.val = p.2.val + 1
  | .west => q.1.val + 1 = p.1.val ∧ q.2 = p.2

instance (d : Direction) (p q : Cell w h) : Decidable (Adjacent d p q) := by
  unfold Adjacent
  split <;> infer_instance

theorem Adjacent.ne {d : Direction} {p q : Cell w h} (hpq : Adjacent d p q) :
    p ≠ q := by
  intro heq
  subst q
  cases d <;> simp [Adjacent] at hpq

theorem Adjacent.reverse {d : Direction} {p q : Cell w h} (hpq : Adjacent d p q) :
    Adjacent d.opposite q p := by
  cases d <;> simpa [Adjacent, Direction.opposite, eq_comm] using hpq

/-- A direction and a starting cell determine at most one next cell. -/
theorem Adjacent.functional {d : Direction} {p q r : Cell w h}
    (hq : Adjacent d p q) (hr : Adjacent d p r) : q = r := by
  cases d <;> simp only [Adjacent] at hq hr <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

/-- Signed coordinate increasing in the direction of travel. -/
def Direction.position (d : Direction) (p : Cell w h) : ℤ :=
  match d with
  | .north => -(p.2.val : ℤ)
  | .east => p.1.val
  | .south => p.2.val
  | .west => -(p.1.val : ℤ)

/-- Coordinate perpendicular to the direction of travel. -/
def Direction.lane (d : Direction) (p : Cell w h) : ℕ :=
  match d with
  | .north | .south => p.1.val
  | .east | .west => p.2.val

theorem Adjacent.position {d : Direction} {p q : Cell w h} (ha : Adjacent d p q) :
    d.position q = d.position p + 1 := by
  cases d <;> simp only [Adjacent, Direction.position] at * <;> omega

theorem Adjacent.lane {d : Direction} {p q : Cell w h} (ha : Adjacent d p q) :
    d.lane q = d.lane p := by
  cases d <;> simp only [Adjacent, Direction.lane] at * <;> omega

/-- The two directional coordinates determine the cell. -/
theorem Direction.cell_ext (d : Direction) {p q : Cell w h}
    (hl : d.lane p = d.lane q) (hp : d.position p = d.position q) : p = q := by
  cases d <;> simp only [Direction.lane, Direction.position] at * <;>
    apply Prod.ext <;> apply Fin.ext <;> omega

theorem adjacent_iff_coordinates (d : Direction) (p q : Cell w h) :
    Adjacent d p q ↔ d.lane q = d.lane p ∧ d.position q = d.position p + 1 := by
  constructor
  · exact fun ha => ⟨ha.lane, ha.position⟩
  · rintro ⟨hl, hp⟩
    cases d <;> simp only [Adjacent, Direction.lane, Direction.position] at * <;>
      constructor <;> omega

end PushPuzzle.PushFS

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Grid
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Logic.Relation

/-!
# Push-kFS and Push-*FS

Fixed walls, unlabelled boxes and exact player positions on a finite rectangle.
A push moves the entire consecutive run in front of the player by one cell.
The cap `none` permits any run length; `some k` permits at most `k` boxes.

## Main definitions

* `Move`, `Step`, `Reachable`: the common operational semantics.
* `Instance.Solvable`: exact storage with unrestricted final player position.

-/

@[expose] public section

namespace PushPuzzle.PushFS


variable {w h : ℕ}

/-- Fixed walls and storage goals. -/
@[ext] structure Board (w h : ℕ) where
  /-- Inaccessible cells. -/
  walls : Finset (Cell w h)
  /-- The required final box set. -/
  goals : Finset (Cell w h)
  deriving DecidableEq

/-- The player and the unlabelled box set. -/
@[ext] structure State (w h : ℕ) where
  /-- Exact player position. -/
  player : Cell w h
  /-- Occupied cells. -/
  boxes : Finset (Cell w h)
  deriving DecidableEq

/-- A state is a player cell and a finite set of occupied cells. -/
def State.equiv : State w h ≃ Cell w h × Finset (Cell w h) where
  toFun s := (s.player, s.boxes)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (State w h) := Fintype.ofEquiv _ State.equiv.symm

/-- The total number of states, including invalid states. -/
theorem State.card : Fintype.card (State w h) = (w * h) * 2 ^ (w * h) := by
  rw [Fintype.card_congr State.equiv]
  simp only [Fintype.card_prod, Fintype.card_finset, Fintype.card_fin]

/-- All actors occupy floor and the player occupies an empty cell. -/
def State.Valid (B : Board w h) (s : State w h) : Prop :=
  s.player ∉ B.walls ∧ Disjoint s.boxes B.walls ∧ s.player ∉ s.boxes

/-- A directed segment from the player through `n` boxes to one empty cell. -/
structure Run (B : Board w h) (d : Direction) (s : State w h) (n : ℕ) where
  /-- The player, then all boxes in order, then the empty destination. -/
  cell : Fin (n + 2) → Cell w h
  /-- The segment starts at the player. -/
  start : cell 0 = s.player
  /-- Consecutive cells are adjacent in the pushing direction. -/
  adjacent : ∀ i : Fin (n + 1), Adjacent d (cell i.castSucc) (cell i.succ)
  /-- The intermediate cells are occupied. -/
  occupied : ∀ i : Fin n, cell ⟨i.val + 1, by omega⟩ ∈ s.boxes
  /-- The destination after the last box is empty. -/
  empty : cell ⟨n + 1, by omega⟩ ∉ s.boxes
  /-- The segment lies on floor. -/
  floor : ∀ i, cell i ∉ B.walls

/-- A finite cap bounds the number of boxes; `none` is unlimited. -/
def Permits (cap : Option ℕ) (n : ℕ) : Prop :=
  match cap with
  | none => True
  | some k => n ≤ k

/-- A walk or a simultaneous push of one complete nonempty consecutive run. -/
inductive Move (B : Board w h) (cap : Option ℕ) (d : Direction) :
    State w h → State w h → Prop
  | walk {s t} (valid : s.Valid B) (adjacent : Adjacent d s.player t.player)
      (floor : t.player ∉ B.walls) (empty : t.player ∉ s.boxes)
      (boxes : t.boxes = s.boxes) : Move B cap d s t
  | push {s t n} (valid : s.Valid B) (positive : 0 < n) (permitted : Permits cap n)
      (run : Run B d s n) (player : t.player = run.cell 1)
      (boxes : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1))) :
      Move B cap d s t

/-- One legal step in any of the four directions. -/
def Step (B : Board w h) (cap : Option ℕ) (s t : State w h) : Prop :=
  ∃ d, Move B cap d s t

/-- Any finite sequence of legal steps, including zero steps. -/
abbrev Reachable (B : Board w h) (cap : Option ℕ) :=
  Relation.ReflTransGen (Step B cap)

/-- A legal explicit rectangular storage instance. -/
structure Instance where
  /-- Rectangle width. -/
  width : ℕ
  /-- Rectangle height. -/
  height : ℕ
  /-- Walls and targets. -/
  board : Board width height
  /-- Starting player and boxes. -/
  initial : State width height
  /-- Targets lie on floor. -/
  goals_floor : Disjoint board.walls board.goals
  /-- The initial state is legal. -/
  initial_valid : initial.Valid board
  /-- All boxes have to be stored. -/
  boxes_eq_goals : initial.boxes.card = board.goals.card

/-- Reach the exact target set; the final player position is unrestricted. -/
def Instance.Solvable (cap : Option ℕ) (I : Instance) : Prop :=
  ∃ t, Reachable I.board cap I.initial t ∧ t.boxes = I.board.goals

/-- The language of solvable storage instances at the specified push limit. -/
def solvable (cap : Option ℕ) : Set Instance := {I | I.Solvable cap}

theorem Move.valid_source {B : Board w h} {cap : Option ℕ} {d : Direction}
    {s t : State w h} (hm : Move B cap d s t) : s.Valid B := by
  cases hm <;> assumption

/-- Relaxing a push limit preserves a move. -/
private theorem Move.mono {B : Board w h} {cap cap' : Option ℕ} {d : Direction}
    {s t : State w h} (hcap : ∀ n, Permits cap n → Permits cap' n)
    (hm : Move B cap d s t) : Move B cap' d s t := by
  cases hm with
  | walk hv ha hf he hb => exact .walk hv ha hf he hb
  | push hv hn hc run hp hb => exact .push hv hn (hcap _ hc) run hp hb

/-- Relaxing a push limit preserves every finite trajectory. -/
theorem Reachable.mono {B : Board w h} {cap cap' : Option ℕ} {s t : State w h}
    (hcap : ∀ n, Permits cap n → Permits cap' n) (hr : Reachable B cap s t) :
    Reachable B cap' s t := by
  induction hr with
  | refl => exact .refl
  | tail _ hs ih => exact ih.tail ⟨hs.choose, hs.choose_spec.mono hcap⟩

/-- Every single-box solution is a solution at any positive finite push limit. -/
theorem Instance.solvable_of_one {k : ℕ} (hk : 1 ≤ k) {I : Instance}
    (hI : I.Solvable (some 1)) : I.Solvable (some k) := by
  obtain ⟨t, hr, ht⟩ := hI
  exact ⟨t, hr.mono (cap' := some k) (fun _ hn => Nat.le_trans hn hk), ht⟩

/-- Removing the push limit preserves solvability. -/
theorem Instance.solvable_unlimited {cap : Option ℕ} {I : Instance}
    (hI : I.Solvable cap) : I.Solvable none := by
  obtain ⟨t, hr, ht⟩ := hI
  exact ⟨t, hr.mono (fun _ _ => trivial), ht⟩

end PushPuzzle.PushFS

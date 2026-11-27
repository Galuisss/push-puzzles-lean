/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Execution
public import PushFS.Labels
public import PushFS.Placement
import Mathlib.Tactic.DeriveFintype

/-!
# The 81 × 107 AND/OR gate tiles

All walls extend to the three open boundary ports. The AND's left arm contains
the protected joint fanout and two turns; each arm contains a passable flip.
The coordinates and movement lists specify the full gate shells.

## Main definitions

* `Signals`, `legal`: the two inward input flags and the outward heavy flag.
* `wallTest`, `board`: the actual long-wall tile.
* `port`, `portDirection`: its three boundary connections.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Gates


/-- Three canonical port flags. The right flag points outward, the other two inward. -/
structure Signals where
  /-- Left port points inward. -/
  left : Bool
  /-- Upper port points inward. -/
  upper : Bool
  /-- Right port points outward. -/
  right : Bool
  deriving DecidableEq

/-- Read the flag of a numbered port, in left/upper/right order. -/
def Signals.get (b : Signals) (i : Fin 3) : Bool :=
  if i = 0 then b.left else if i = 1 then b.upper else b.right

/-- NCL legality for the physical three trigger positions: `true` selects AND. -/
def legal (kind : Bool) (b : Signals) : Prop :=
  b.right = true → if kind then b.left = true ∧ b.upper = true
    else b.left = true ∨ b.upper = true

instance (kind : Bool) (b : Signals) : Decidable (legal kind b) := by
  unfold legal
  infer_instance

/-- Exactly one of the three canonical port flags changes. -/
def singleChange (a b : Signals) : Prop :=
  (a.left ≠ b.left ∧ a.upper = b.upper ∧ a.right = b.right) ∨
  (a.left = b.left ∧ a.upper ≠ b.upper ∧ a.right = b.right) ∨
  (a.left = b.left ∧ a.upper = b.upper ∧ a.right ≠ b.right)

instance (a b : Signals) : Decidable (singleChange a b) := by
  unfold singleChange
  infer_instance

/-- The changed port of a single-change pair. -/
def changingPort (a b : Signals) : Fin 3 :=
  if a.left = b.left then if a.upper = b.upper then 2 else 1 else 0

/-- The coordinate type of each long-wall tile. -/
abbrev C := Cell 81 107

/-- A common exact starting and ending player cell for all macros. -/
def hub : C := (40, 82)

def andWallTest (p : C) : Bool :=
  let x : ℤ := (p.1.val : ℤ) - 40
  let y : ℤ := (p.2.val : ℤ) - 90
  decide (((y = 1 ∨ y = 2) ∧ ((-3 ≤ x ∧ x ≤ 20) ∨ x = 22 ∨ x = 23)) ∨
    ((y = -1 ∨ y = -2) ∧ (x = 20 ∨ x = 21 ∨ 23 ≤ x)) ∨
    ((x = -3 ∨ x = -2) ∧ ((-21 ≤ y ∧ y ≤ 2) ∨ y = -23 ∨ y = -24)) ∨
    ((x = 0 ∨ x = 1) ∧ (y = -21 ∨ y = -22 ∨ (-63 ≤ y ∧ y ≤ -24))) ∨
    ((y = -63 ∨ y = -62) ∧ (x = -21 ∨ x = -20 ∨ (-18 ≤ x ∧ x ≤ 1))) ∨
    ((y = -60 ∨ y = -59) ∧ (x ≤ -21 ∨ x = -19 ∨ x = -18)) ∨
    ((x = 4 ∨ x = 5) ∧ ((-71 ≤ y ∧ y ≤ -1) ∨ y = -73 ∨ y = -74)) ∨
    ((x = 1 ∨ x = 2) ∧ (y = -71 ∨ y = -72 ∨ y ≤ -74)))

def orWallTest (p : C) : Bool :=
  let x : ℤ := (p.1.val : ℤ) - 40
  let y : ℤ := (p.2.val : ℤ) - 90
  decide (((y = 1 ∨ y = 2) ∧ (x = -20 ∨ x = -19 ∨ (-17 ≤ x ∧ x ≤ 21) ∨ x = 23 ∨ x = 24)) ∨
    ((y = -1 ∨ y = -2) ∧ (x ≤ -20 ∨ x = -18 ∨ x = -17 ∨ x = 21 ∨ x = 22 ∨ 24 ≤ x)) ∨
    ((x = 5 ∨ x = 6) ∧ ((-71 ≤ y ∧ y ≤ -1) ∨ y = -73 ∨ y = -74)) ∨
    ((x = 2 ∨ x = 3) ∧ (y = -71 ∨ y = -72 ∨ y ≤ -74)))

def wallTest (kind : Bool) (p : C) : Bool := if kind then andWallTest p else orWallTest p

def trackTest (kind : Bool) (p : C) : Bool :=
  if kind then decide ((p.2.val = 90 ∧ 39 ≤ p.1.val) ∨
    (p.1.val = 39 ∧ 29 ≤ p.2.val ∧ p.2.val ≤ 90) ∨
    (p.2.val = 29 ∧ p.1.val ≤ 39) ∨ (p.1.val = 43 ∧ p.2.val < 90))
  else decide (p.2.val = 90 ∨ (p.1.val = 44 ∧ p.2.val < 90))

def crossingTest (kind : Bool) (p : C) : Bool :=
  if kind then decide (p = (39,68) ∨ p = (39,67) ∨ p = (20,29) ∨ p = (21,29) ∨
    p = (43,18) ∨ p = (43,17) ∨ p = (61,90) ∨ p = (62,90))
  else decide (p = (21,90) ∨ p = (22,90) ∨ p = (44,18) ∨ p = (44,17) ∨
    p = (62,90) ∨ p = (63,90))

def reservedTest (kind : Bool) (p : C) : Bool :=
  trackTest kind p && !crossingTest kind p

/-- The complete fixed wall set. -/
def walls (kind : Bool) : Finset C := Finset.univ.filter fun p => wallTest kind p

/-- Cells reserved for canonical tracks, excluding the designated walking crossings. -/
def reserved (kind : Bool) : Finset C := Finset.univ.filter fun p => reservedTest kind p

/-- All rail cells, including the protected turns and sink junctions. -/
def tracks (kind : Bool) : Finset C := Finset.univ.filter fun p => trackTest kind p

/-- The actual tile board; the goal set is supplied independently. -/
def board (kind : Bool) (goals : Finset C) : Board 81 107 := ⟨walls kind, goals⟩

/-- Boundary connections in left/upper/right order. -/
def port (kind : Bool) (i : Fin 3) : C :=
  if i = 0 then if kind then (0, 29) else (0, 90)
  else if i = 1 then if kind then (43, 0) else (44, 0)
  else (80, 90)

/-- Direction pointing out of the tile at each numbered port. -/
def portDirection (i : Fin 3) : Direction :=
  if i = 0 then .west else if i = 1 then .north else .east

@[simp] theorem mem_walls (kind : Bool) (p : C) : p ∈ walls kind ↔ wallTest kind p = true := by
  simp [walls]

@[simp] theorem mem_reserved (kind : Bool) (p : C) :
    p ∈ reserved kind ↔ reservedTest kind p = true := by simp [reserved]

theorem wallTest_correct (kind : Bool) (goals : Finset C) (p : C) :
    wallTest kind p = true ↔ p ∈ (board kind goals).walls := (mem_walls kind p).symm

end PushPuzzle.PushFS.Gadgets.Gates

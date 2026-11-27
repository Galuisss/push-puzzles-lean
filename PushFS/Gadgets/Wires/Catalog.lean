/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Interface
public import PushFS.Gadgets.Wires.Straight
public import PushFS.Gadgets.Wires.Parity
public import PushFS.Gadgets.Wires.Flip
public import PushFS.Gadgets.Wires.Turn

/-! The four finite wire templates available to an explicit bitmap compiler. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires


/-- A straight double flip, odd-span parity adjuster, single flip, or guarded right turn. -/
inductive Kind
  | straight | parity | flip | turn
  deriving DecidableEq

instance : Fintype Kind where
  elems := {.straight, .parity, .flip, .turn}
  complete k := by cases k <;> simp

/-- Full rectangle width, including overlapping collars. -/
def Kind.width : Kind → ℕ
  | .straight => 45 | .parity => 64 | .flip => 25 | .turn => 45

/-- Full rectangle height. -/
def Kind.height : Kind → ℕ
  | .turn => 41 | _ => 21

/-- The exact number of physical boxes. -/
def Kind.count : Kind → ℕ
  | .straight => 18 | .parity => 26 | .flip => 9 | .turn => 29

/-- Complete coordinates, static bitmap and executable phase-change programs. -/
def Kind.template (k : Kind) : Template k.width k.height k.count :=
  match k with
  | .straight => Straight.template
  | .parity => Parity.template
  | .flip => Flip.template
  | .turn => Turn.template

/-- Every catalog entry carries all concrete physical and execution proofs. -/
theorem Kind.checked (k : Kind) : k.template.Checked := by
  cases k
  · exact Straight.checked
  · exact Parity.checked
  · exact Flip.checked
  · exact Turn.checked

/-- Seam anchors in the local coordinate convention of each concrete tile. -/
def Kind.port (k : Kind) : Fin 2 → Cell k.width k.height :=
  match k with
  | .straight => Straight.port
  | .parity => Parity.port
  | .flip => Flip.port
  | .turn => Turn.port

/-- First physical endpoint identity. -/
def Kind.firstIndex (k : Kind) : Fin k.count := ⟨0, by cases k <;> decide⟩

/-- Last physical endpoint identity. -/
def Kind.lastIndex (k : Kind) : Fin k.count :=
  ⟨k.count - 1, by cases k <;> decide⟩

/-- Exact canonical physical box at either endpoint, including its selected phase. -/
def Kind.endpoint (k : Kind) (phase : Bool) (i : Fin 2) : Cell k.width k.height :=
  k.template.position phase (if i = 0 then k.firstIndex else k.lastIndex)

end PushPuzzle.PushFS.Gadgets.Wires

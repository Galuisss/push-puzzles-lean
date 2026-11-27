/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Basic
public import Mathlib.Data.Fin.VecNotation

/-!
# A flip wire tile

A 25 × 21 bitmap with 9 boxes and explicit move programs for both phase changes.
The programs include the player's walks.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Flip


-- Kernel replay reduces the finite slot arrays and explicit direction programs.
set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev C := Cell 25 21
def hub : C := (12, 3)
def corner (i : Fin 4) : C := ![(1, 1), (23, 1), (1, 19), (23, 19)] i

def wallTest (p : C) : Bool :=
  let x := p.1.val
  let y := p.2.val
  decide (((y=8 ∨ y=9) ∧ (x=8 ∨ x=9 ∨ 11 ≤ x)) ∨
    ((y=11 ∨ y=12) ∧ (x ≤ 8 ∨ x=10 ∨ x=11)))

def reservedTest (p : C) : Bool := decide (p.2.val=10 ∧ p.1.val ≠ 9 ∧ p.1.val ≠ 10)
def neighbors : Finset C := {(0, 10), (23, 10)}

def low : Fin 9 → Fin 25 := ![2, 4, 6, 8, 12, 14, 16, 18, 20]
def high : Fin 9 → Fin 25 := ![3, 5, 7, 11, 13, 15, 17, 19, 21]

def forward : List Direction := [.west, .west, .south, .south, .south, .south, .south, .south, .south, .west, .south, .south, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .south, .south, .west, .west, .west, .north, .north, .north, .east, .east, .east, .west, .west, .north, .north, .north, .west, .west, .west, .south, .south, .south, .east, .east, .east, .west, .west, .west, .north, .west, .west, .south, .east, .west, .north, .west, .west, .south, .east, .west, .north, .west, .west, .south, .east, .north, .east, .east, .east, .east, .east, .north, .north, .east, .east, .east, .east, .east, .north, .north, .north, .north]

def backward : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .west, .east, .north, .east, .east, .south, .west, .east, .north, .east, .north, .north, .east, .east, .east, .south, .south, .south, .west, .west, .west, .east, .east, .south, .south, .south, .east, .east, .east, .north, .north, .north, .west, .west, .west, .east, .east, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .west, .west, .west, .north, .north, .north, .east, .north, .north, .north, .east, .east, .north, .north, .north, .north]

def walk0 : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .north, .north]

def walk1 : List Direction := [.east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north]

def walk2 : List Direction := [.west, .west, .south, .south, .south, .south, .south, .south, .south, .west, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south]

def walk3 : List Direction := [.west, .west, .south, .south, .south, .south, .south, .south, .south, .west, .south, .south, .south, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south]

/-- The complete physical and program data of this finite tile. -/
def template : Template 25 21 9 where
  hub := hub
  corner := corner
  wall := wallTest
  reserved := reservedTest
  neighbors := neighbors
  zero i := (low i, 10)
  one i := (high i, 10)
  forward := forward
  backward := backward
  walks := ![walk0, walk1, walk2, walk3]

/-- Every literal program and physical slot is independently checked by the kernel. -/
theorem checked : template.Checked where
  injective := by decide +kernel
  slots_reserved := by decide +kernel
  neighbors_reserved := by decide +kernel
  neighbors_floor := by decide +kernel
  static_paths := by decide +kernel
  forward_checked := by decide +kernel
  backward_checked := by decide +kernel
  walks_checked := by decide +kernel

/-- Translation distance between successive five-column-overlap tiles. -/
def span : ℕ := 20

/-- The two seam anchors; the rectangle extends two cells to either side. -/
def port (i : Fin 2) : C := if i = 0 then (2, 10) else (22, 10)

/-- Exact canonical endpoint positions, before and after the phase change. -/
theorem endpoint_slots : ∀ phase : Bool,
    (template.position phase 0).1.val = 2 + phase.toNat ∧
    (template.position phase 8).1.val = span + phase.toNat := by decide +kernel

/-- The complete wall stencil in the five-column left collar. -/
theorem left_collar : ∀ p : C, p.1.val < 5 →
    wallTest p = decide (p.2.val = 11 ∨ p.2.val = 12) := by decide +kernel

/-- The complete wall stencil in the five-column right collar. -/
theorem right_collar : ∀ p : C, span ≤ p.1.val →
    wallTest p = decide (p.2.val = 8 ∨ p.2.val = 9) := by decide +kernel

/-- Every rail cell has a protecting wall on at least one perpendicular side. -/
theorem rail_guard : ∀ x : Fin 25, wallTest (x,9) = true ∨ wallTest (x,11) = true := by
  decide +kernel

/-- The physical identities occur in their fixed left-to-right order in both phases. -/
theorem ordered_slots : ∀ (phase : Bool) (i j), i < j →
    (template.position phase i).1.val < (template.position phase j).1.val := by decide +kernel

/-- Every canonical target set has no adjacent box pair. -/
theorem sparse_slots : ∀ (phase : Bool) (i j) (d : Direction),
    ¬Adjacent d (template.position phase i) (template.position phase j) := by decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.Flip

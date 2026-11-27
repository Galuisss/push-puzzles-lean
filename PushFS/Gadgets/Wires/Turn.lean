/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Basic

/-!
# A concrete 45 × 41 guarded right turn with one passable flip

The tile specifies all 29 physical boxes, both complete phase-change programs,
and all player walks.
The horizontal arm meets the vertical arm at the protected non-goal sink (10,9).
-/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Turn


-- Kernel replay reduces the finite slot array and explicit direction programs.
set_option maxRecDepth 65536
set_option maxHeartbeats 0

abbrev C := Cell 45 41
def hub : C := (38,20)
def corner (i : Fin 4) : C := if i=0 then (1,1) else if i=1 then (43,1) else if i=2 then (1,39) else (43,39)
def wallTest (p : C) : Bool :=
  let x : ℤ := (p.1.val : ℤ)-40
  let y : ℤ := (p.2.val : ℤ)+20
  decide (((y=30 ∨ y=31) ∧ (x = -9 ∨ x = -8 ∨ -6 ≤ x)) ∨
    ((y=27 ∨ y=28) ∧ -32 ≤ x ∧ (x ≤ -9 ∨ x = -7 ∨ x = -6)) ∨
    ((x = -32 ∨ x = -31) ∧ 27 ≤ y))
def trackTest (p : C) : Bool := decide ((p.2.val=9 ∧ 10 ≤ p.1.val) ∨ (p.1.val=10 ∧ 9 ≤ p.2.val))
def reservedTest (p : C) : Bool := trackTest p && decide (p ≠ (32,9) ∧ p ≠ (33,9))
/-- Actual horizontal neighboring box positions, left fixed during either propagation. -/
def neighbors : Finset C := {(42,9), (44,9)}

def slots : List (C × C) :=
  [((40,9),(39,9)),
   ((38,9),(37,9)),
   ((36,9),(35,9)),
   ((34,9),(31,9)),
   ((30,9),(29,9)),
   ((28,9),(27,9)),
   ((26,9),(25,9)),
   ((24,9),(23,9)),
   ((22,9),(21,9)),
   ((20,9),(19,9)),
   ((18,9),(17,9)),
   ((16,9),(15,9)),
   ((14,9),(13,9)),
   ((12,9),(11,9)),
   ((10,10),(10,11)),
   ((10,12),(10,13)),
   ((10,14),(10,15)),
   ((10,16),(10,17)),
   ((10,18),(10,19)),
   ((10,20),(10,21)),
   ((10,22),(10,23)),
   ((10,24),(10,25)),
   ((10,26),(10,27)),
   ((10,28),(10,29)),
   ((10,30),(10,31)),
   ((10,32),(10,33)),
   ((10,34),(10,35)),
   ((10,36),(10,37)),
   ((10,38),(10,39))]

def forward : List Direction := [.west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .north, .north, .north, .west, .south, .east, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .east, .north, .west, .east, .south, .east, .south, .south, .east, .east, .east, .north, .north, .north, .west, .west, .west, .east, .east, .north, .north, .north, .east, .east, .east, .south, .south, .south, .west, .west, .west, .east, .east, .east, .north, .east, .east, .south, .west, .east, .north, .east, .east, .south, .west, .east, .north, .east, .east, .south, .west, .north, .west, .west, .west, .west, .west, .north, .north, .west, .west, .west, .south, .south, .south, .east, .south, .south, .south, .east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south, .south, .south]

def backward : List Direction := [.west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .north, .north, .north, .east, .east, .east, .east, .east, .east, .south, .south, .south, .east, .west, .north, .west, .west, .south, .east, .west, .north, .west, .north, .north, .west, .west, .west, .south, .south, .south, .east, .east, .east, .west, .west, .south, .south, .south, .west, .west, .west, .north, .north, .north, .east, .east, .east, .west, .west, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .west, .south, .west, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .south, .south, .south, .west, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north]

def walk0 : List Direction := [.west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .north, .north, .north, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .north, .north, .north, .north, .north]

def walk1 : List Direction := [.west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .north, .north]

def walk2 : List Direction := [.west, .west, .west, .west, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .north, .north, .north, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]

def walk3 : List Direction := [.east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]

/-- The complete physical and program data of the guarded turn. -/
def template : Template 45 41 29 where
  hub := hub
  corner := corner
  wall := wallTest
  reserved := reservedTest
  neighbors := neighbors
  zero i := (slots.get i).1
  one i := (slots.get i).2
  forward := forward
  backward := backward
  walks i := if i = 0 then walk0 else if i = 1 then walk1 else if i = 2 then walk2 else walk3

/-- Every program and physical slot is independently checked by the kernel. -/
theorem checked : template.Checked where
  injective := by decide +kernel
  slots_reserved := by decide +kernel
  neighbors_reserved := by decide +kernel
  neighbors_floor := by decide +kernel
  static_paths := by decide +kernel
  forward_checked := by decide +kernel
  backward_checked := by decide +kernel
  walks_checked := by decide +kernel

/-- Seam anchors of the east and south connections. -/
def port (i : Fin 2) : C := if i = 0 then (42,9) else (10,40)

/-- The complete south collar wall stencil. -/
theorem south_collar : ∀ p : C, 36 ≤ p.2.val →
    wallTest p = decide (p.1.val = 8 ∨ p.1.val = 9) := by decide +kernel

/-- Every canonical target set has no adjacent box pair, including across the corner. -/
theorem sparse_slots : ∀ (phase : Bool) (i j) (d : Direction),
    ¬Adjacent d (template.position phase i) (template.position phase j) := by decide +kernel

/-- Two actual walls make the corner a static box trap. -/
theorem corner_immobile (goals : Finset C) : ∀ q, ¬Displacement (template.board goals) (10,9) q := by
  intro q hd
  obtain ⟨_, d, rear, hr, hq, hrw, hqw⟩ := hd
  have hn : Adjacent .north ((10,9) : C) (10,8) := by decide
  have hw : Adjacent .west ((10,9) : C) (9,9) := by decide
  have hNW : (10,8) ∈ template.walls := (template.mem_walls _).mpr (by decide +kernel)
  have hWW : (9,9) ∈ template.walls := (template.mem_walls _).mpr (by decide +kernel)
  cases d with
  | north => exact hqw (hq.functional hn ▸ hNW)
  | east => exact hrw (hr.reverse.functional hw ▸ hWW)
  | south => exact hrw (hr.reverse.functional hn ▸ hNW)
  | west => exact hqw (hq.functional hw ▸ hWW)

end PushPuzzle.PushFS.Gadgets.Wires.Turn

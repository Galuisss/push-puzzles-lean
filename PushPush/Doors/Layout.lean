/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
import Mathlib.Data.List.FinRange

/-! Uniform rack chambers and private six-pin wires. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors

open PushFS (Cell State)

/-- A wire joins one westward launch to one eastward arrival. -/
@[ext] structure Wire where
  /-- Launch row before the common vertical translation. -/
  source : ℕ
  /-- The launch moves away from its room blocker towards the south. -/
  sourceSouth : Bool
  /-- Arrival row before the common vertical translation. -/
  target : ℕ
  /-- The terminal pin is south of the arrival row. -/
  targetSouth : Bool
  deriving DecidableEq

/-- A chamber-and-wire description before rasterization. -/
@[ext] structure Layout where
  /-- Last chamber's southern divider. -/
  depth : ℕ
  /-- Rows with rack boxes. -/
  rackRows : List ℕ
  /-- Chamber dividers; their rack neighbours are included automatically. -/
  dividers : List ℕ
  /-- Endpoint blockers two rows from a chamber divider. -/
  caps : List ℕ
  /-- Initial door storage rows. -/
  dataRows : List ℕ
  /-- Terminal door storage rows. -/
  goalRows : List ℕ
  /-- Initial signal row. -/
  launch : ℕ
  /-- Terminal signal row. -/
  stop : ℕ
  /-- Private routing wires. -/
  wires : List Wire
  deriving DecidableEq

namespace Layout

/-- Empty outer bands contain the private wire levels. -/
def shift (L : Layout) : ℕ := 20 * L.wires.length + 15

/-- The rack lies to the east of all wire columns. -/
def rackX (L : Layout) : ℕ := 30 * L.wires.length + 40

/-- Six cells of free margin east of the rack. -/
def width (L : Layout) : ℕ := L.rackX + 6

/-- Two private level bands surround the chamber stack. -/
def height (L : Layout) : ℕ := L.depth + 2 * L.shift + 1

/-- Wire `i`'s first private vertical column. -/
def wireA (i : ℕ) : ℕ := 30 * i + 8

/-- Wire `i`'s second private vertical column. -/
def wireB (i : ℕ) : ℕ := 30 * i + 24

/-- Wire `i`'s final private vertical column. -/
def wireC (i : ℕ) : ℕ := 30 * i + 15

/-- A private row in one of the two outer bands. -/
def level (L : Layout) (i : ℕ) (south : Bool) : ℕ :=
  if south then L.depth + L.shift + 10 + 10 * i else 5 + 10 * i

/-- First horizontal outer leg. -/
def wireY (L : Layout) (i : ℕ) (e : Wire) : ℕ := L.level (2 * i) e.sourceSouth

/-- Second horizontal outer leg. -/
def wireV (L : Layout) (i : ℕ) (e : Wire) : ℕ := L.level (2 * i + 1) (!e.targetSouth)

/-- The adjacent row on a specified side. -/
def beside (south : Bool) (y : ℕ) : ℕ := if south then y + 1 else y - 1

/-- The six ordinary boxes that stop the successive wire slides. -/
def wirePins (L : Layout) (i : ℕ) (e : Wire) : List (ℕ × ℕ) :=
  let a := wireA i
  let b := wireB i
  let c := wireC i
  let y := L.wireY i e
  let v := L.wireV i e
  [(a - 1, e.source + L.shift), (a, beside e.sourceSouth y),
    (b + 1, y), (b, beside (decide (y < v)) v), (c - 1, v),
    (c, beside e.targetSouth (e.target + L.shift))]

/-- All fixed wire pins, retaining the original wire index. -/
def pins (L : Layout) : Finset (ℕ × ℕ) :=
  (L.wires.zipIdx.flatMap fun (e, i) => L.wirePins i e).toFinset

/-- The eight successive positions of the travelling signal. -/
def wirePath (L : Layout) (i : ℕ) (e : Wire) : List (ℕ × ℕ) :=
  let a := wireA i
  let b := wireB i
  let c := wireC i
  let y := L.wireY i e
  let v := L.wireV i e
  [(L.rackX - 1, e.source + L.shift), (a, e.source + L.shift),
    (a, y), (b, y), (b, v), (c, v), (c, e.target + L.shift),
    (L.rackX - 1, e.target + L.shift)]

/-- Rack rows include the two neighbours of every translated divider. -/
def rack (L : Layout) : Finset (ℕ × ℕ) :=
  ((L.rackRows.map fun y => (L.rackX, y + L.shift)) ++
    L.dividers.flatMap (fun y =>
      [(L.rackX, y + L.shift - 1), (L.rackX, y + L.shift + 1)])).toFinset

/-- Chamber separators and endpoint caps. -/
def blockers (L : Layout) : Finset (ℕ × ℕ) :=
  ((L.dividers ++ L.caps).map fun y => (L.rackX - 1, y + L.shift)).toFinset

/-- Static inventory common to the initial and terminal box sets. -/
def fixed (L : Layout) : Finset (ℕ × ℕ) := L.pins ∪ L.rack ∪ L.blockers

/-- The initial boxes, including all door bits and the unique travelling signal. -/
def initialRaw (L : Layout) : Finset (ℕ × ℕ) :=
  L.fixed ∪ ((L.launch :: L.dataRows).map fun y => (L.rackX - 1, y + L.shift)).toFinset

/-- Exact terminal inventory, including the cleanup slots and final signal. -/
def goalsRaw (L : Layout) : Finset (ℕ × ℕ) :=
  L.fixed ∪ ((L.stop :: L.goalRows).map fun y => (L.rackX - 1, y + L.shift)).toFinset

/-- Rasterize the explicitly listed coordinates on the finite rectangle. -/
def raster (L : Layout) (boxes : Finset (ℕ × ℕ)) : Finset (Cell L.width L.height) :=
  Finset.univ.filter fun p => (p.1.val, p.2.val) ∈ boxes

@[simp] theorem mem_raster (L : Layout) (boxes : Finset (ℕ × ℕ))
    (p : Cell L.width L.height) : p ∈ L.raster boxes ↔ (p.1.val, p.2.val) ∈ boxes := by
  simp [raster]

theorem width_pos (L : Layout) : 0 < L.width := by unfold width; omega

theorem height_pos (L : Layout) : 0 < L.height := by unfold height; omega

/-- The initial player uses the empty southeast corner. -/
def corner (L : Layout) : Cell L.width L.height :=
  (⟨L.width - 1, by have := L.width_pos; omega⟩,
    ⟨L.height - 1, by have := L.height_pos; omega⟩)

/-- The actual initial state of the finite wall-free board. -/
def initial (L : Layout) : State L.width L.height := ⟨L.corner, L.raster L.initialRaw⟩

end Layout
end PushPuzzle.PushPush.Doors

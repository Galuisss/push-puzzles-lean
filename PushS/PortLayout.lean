/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PageLevels
public import PushS.Scales
public import PushS.Shuttle
public import Mathlib.Data.List.GetD

/-!
# Two-page port data and canonical internal signals

The layout retains the actual ordered upper pairs and the labelled lower groups. Forgetting
the AND/OR label gives the existing `PageLevels.Pages`, so working levels are computed from
the actual input. Physical internal bits follow the Python board's edge order. Coordinate
reads use tables bounded by the explicitly supplied scale environment.

## Main definitions

* `PortLayout`: raw ordered pairs and labelled lower groups.
* `SignalState`: axis bits followed by the physical internal edge bits.
* `PortLayout.canonical`: fill all internal bits from the interface axes.
* `PortLayout.readDepth`, `PortLayout.readLength`: bounded working-coordinate reads.
-/

public section

namespace PushPuzzle.PushS


/-- A lower WIRE, or three consecutive ports with their actual AND/OR label. -/
inductive LowerGroup where
  /-- An ordinary pair of ports. -/
  | wire (left right : ℕ)
  /-- A gate on ports `first`, `first + 1`, `first + 2`. -/
  | gate (kind : Shuttle.Kind) (first : ℕ)
  deriving DecidableEq

namespace LowerGroup

/-- Forget the gate label to compute the working levels. -/
@[expose] def shape : LowerGroup → PageLevels.Group
  | .wire a b => .wire a b
  | .gate _ a => .triple a

/-- Number of physical internal edges: one horizontal wire, or left/short/right trains. -/
@[expose] def internalCount : LowerGroup → ℕ
  | .wire .. => 1
  | .gate .. => 3

end LowerGroup

/-- The actual two-page port order, before any geometric interpretation. -/
structure PortLayout where
  /-- Ports are numbered from zero to this count minus one. -/
  portCount : ℕ
  /-- Mathematical ordered pairs of upper ports, left endpoint first. -/
  upperPairs : List (ℕ × ℕ)
  /-- Ordered lower WIRE and labelled consecutive three-port groups. -/
  lowerGroups : List LowerGroup

/-- Physical signals in axis order and then upper/lower internal edge order. -/
structure SignalState where
  /-- One bit per vertical axis; true supplies the upper endpoint. -/
  axes : List Bool
  /-- Upper WIREs first, then each lower WIRE or left/short/right triple. -/
  internal : List Bool

namespace PortLayout

/-- The actual pages used by the existing active-interval level algorithm. -/
@[expose] def pages (l : PortLayout) : PageLevels.Pages where
  portCount := l.portCount
  upper := l.upperPairs.map fun (a, b) => .wire a b
  lower := l.lowerGroups.map LowerGroup.shape

/-- Read the computed working level of an upper group by its actual list index. -/
@[expose] def upperLevel (l : PortLayout) (i : ℕ) : ℕ :=
  l.pages.levels.1.getD i 0

/-- Read the computed working level of a lower group by its actual list index. -/
@[expose] def lowerLevel (l : PortLayout) (i : ℕ) : ℕ :=
  l.pages.levels.2.getD i 0

/-- Internal-edge offset of a lower group, after every upper WIRE. -/
@[expose] def lowerOffset (l : PortLayout) (i : ℕ) : ℕ :=
  l.upperPairs.length + ((l.lowerGroups.take i).map LowerGroup.internalCount).sum

/-- The unique canonical internal filling of the given interface bits. -/
@[expose] def canonical (l : PortLayout) (axes : List Bool) : SignalState where
  axes := axes
  internal := (l.upperPairs.map fun (a, _) => !(axes.getD a false)) ++
    l.lowerGroups.flatMap fun g => match g with
      | .wire a _ => [axes.getD a false]
      | .gate _ a =>
        let heavy := !(axes.getD (a + 2) false)
        [axes.getD a false, heavy, heavy]

/-- The bounded depth table: zero followed by the allocated working rows. -/
@[expose] def depthTable (p : Scales.Parameters) : List ℕ :=
  0 :: (List.range p.levels).map fun j => p.Y (j + 1)

/-- The bounded long-branch table: zero followed by the allocated branch lengths. -/
@[expose] def lengthTable (p : Scales.Parameters) : List ℕ :=
  0 :: (List.range p.levels).map fun j => p.L (j + 1)

/-- Read an allocated working row, using zero for a raw level outside the fixed table. -/
@[expose] def readDepth (p : Scales.Parameters) (j : ℕ) : ℕ :=
  (depthTable p).getD j 0

/-- Read an allocated branch length, using zero outside the fixed table. -/
@[expose] def readLength (p : Scales.Parameters) (j : ℕ) : ℕ :=
  (lengthTable p).getD j 0

/-- Raw levels above the allocated bound read zero without evaluating a new power. -/
theorem readDepth_eq_zero (p : Scales.Parameters) {j : ℕ} (hj : p.levels < j) :
    readDepth p j = 0 := by
  apply List.getD_eq_default
  simp only [depthTable, List.length_cons, List.length_map, List.length_range]
  omega

/-- Raw branch levels above the allocated bound also read zero. -/
theorem readLength_eq_zero (p : Scales.Parameters) {j : ℕ} (hj : p.levels < j) :
    readLength p j = 0 := by
  apply List.getD_eq_default
  simp only [lengthTable, List.length_cons, List.length_map, List.length_range]
  omega

/-- Every valid positive working level reads the literal geometric depth. -/
theorem readDepth_eq (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    readDepth p j = p.Y j := by
  cases j with
  | zero => omega
  | succ j =>
    simp only [readDepth, depthTable, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]

/-- Every valid positive working level reads the literal geometric branch length. -/
theorem readLength_eq (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    readLength p j = p.L j := by
  cases j with
  | zero => omega
  | succ j =>
    simp only [readLength, lengthTable, List.getD_cons_succ]
    rw [List.getD_eq_getElem _ _ (by simp only [List.length_map, List.length_range]; omega)]
    simp only [List.getElem_map, List.getElem_range]

end PortLayout
end PushPuzzle.PushS

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.HoleState
public import PushS.Encoding
public import PushFS.Reduction.Segments

/-!
# Compiling closed hole segments to a wall-free storage instance

The raw recipe specifies a rectangle, a player, and the initial and target hole segments.
The emitter scans their unions at each grid cell. Its wall flag is false, while boxes and
goals are the complements of the corresponding hole unions. Valid recipes construct actual
wall-free instances through `HoleState` and `Instance.ofHoles`.

## Main definitions

* `SegmentRecipe`: proof-free dimensions, player coordinates, and closed hole segments.
* `SegmentRecipe.emit`: the actual dense output algorithm.
* `SegmentRecipe.toInstance`: the semantic wall-free instance of a valid recipe.

## Main results

* `SegmentRecipe.data_eq`: the emitted data equal the actual instance data.
-/

public section

namespace PushPuzzle.PushS


open PushFS PushFS.Reduction
open _root_.Turing.MultiTapeTM

/-- A complete hole-segment recipe before checking its player and storage inventories. -/
structure SegmentRecipe where
  /-- Number of columns in the explicit output rectangle. -/
  width : ℕ
  /-- Number of rows in the explicit output rectangle. -/
  height : ℕ
  /-- Initial player's horizontal coordinate. -/
  playerX : ℕ
  /-- Initial player's vertical coordinate. -/
  playerY : ℕ
  /-- Closed segments whose union is initially empty. -/
  initialSegments : List Segment
  /-- Closed segments whose union is empty in the storage target. -/
  targetSegments : List Segment

/-- Unary dimensions, player coordinates, and the existing framed unary segment encoding. -/
enc_structure encSegmentRecipe : SegmentRecipe where
  width : encUnary, height : encUnary, playerX : encUnary, playerY : encUnary,
  initialSegments : (encList encSegment), targetSegments : (encList encSegment)

namespace SegmentRecipe

/-- A segment list and a queried unary coordinate pair. -/
abbrev encHoleQuery : (List Segment × ℕ × ℕ) ↪ List Bool :=
  encPair (encList encSegment) Bitmap.encPoint

/-- A recipe and a queried unary coordinate pair. -/
abbrev encQuery : (SegmentRecipe × ℕ × ℕ) ↪ List Bool :=
  encPair encSegmentRecipe Bitmap.encPoint

/-- Test membership in the complete union of the represented segment cells. -/
@[expose] def holeTest (q : List Segment × ℕ × ℕ) : Bool :=
  (q.1.flatMap Segment.cells).contains q.2

/-- The executable union test recognizes exactly the represented closed segments. -/
theorem holeTest_eq_true (ss : List Segment) (p : ℕ × ℕ) :
    holeTest (ss, p) = true ↔ ∃ s ∈ ss, s.Contains p := by
  simp [holeTest, List.mem_flatMap, Segment.mem_cells]

/-- The segment union restricted to the declared finite rectangle. -/
@[expose] def holes (w h : ℕ) (ss : List Segment) : Finset (Cell w h) :=
  Finset.univ.filter fun p => holeTest (ss, p.1.val, p.2.val) = true

/-- A finite cell belongs to the hole set exactly when it belongs to a listed segment. -/
theorem mem_holes {w h : ℕ} (ss : List Segment) (p : Cell w h) :
    p ∈ holes w h ss ↔ ∃ s ∈ ss, s.Contains (p.1.val, p.2.val) := by
  simp [holes, holeTest_eq_true]

/-- The player is an actual initial hole, and the initial and target inventories agree. -/
structure Valid (r : SegmentRecipe) : Prop where
  /-- The player lies inside the declared width. -/
  playerX_lt : r.playerX < r.width
  /-- The player lies inside the declared height. -/
  playerY_lt : r.playerY < r.height
  /-- The initial segment union contains the player. -/
  player_empty : holeTest (r.initialSegments, r.playerX, r.playerY) = true
  /-- Taking complements gives equally many initial boxes and storage goals. -/
  card_eq : (holes r.width r.height r.initialSegments).card =
    (holes r.width r.height r.targetSegments).card

/-- Inspect one cell of the actual no-wall dense output. -/
@[expose] def tile : SegmentRecipe × ℕ × ℕ → Encoding.Tile
  | (r, x, y) =>
    ⟨false, !(holeTest (r.targetSegments, x, y)), !(holeTest (r.initialSegments, x, y)),
      decide (x = r.playerX ∧ y = r.playerY)⟩

/-- Emit every cell of the explicit rectangle in the standard row order. -/
@[expose] def emit (r : SegmentRecipe) : Encoding.Data :=
  ⟨r.width, r.height, (List.range r.height).map fun y =>
    (List.range r.width).map fun x => tile (r, x, y)⟩

/-- Construct the genuine wall-free storage instance, with boxes equal to the hole complement. -/
@[expose] def toInstance (r : SegmentRecipe) (h : r.Valid) : Instance :=
  Instance.ofHoles
    { player := (⟨r.playerX, h.playerX_lt⟩, ⟨r.playerY, h.playerY_lt⟩)
      empty := holes r.width r.height r.initialSegments
      player_empty := by simpa only [holes, Finset.mem_filter, Finset.mem_univ, true_and] using
        h.player_empty }
    (holes r.width r.height r.targetSegments) h.card_eq

/-- Each emitted flag is the flag of the actual compiled instance. -/
private theorem tile_eq (r : SegmentRecipe) (h : r.Valid) (p : Cell r.width r.height) :
    tile (r, p.1.val, p.2.val) =
      Encoding.tile (r.toInstance h).board (r.toInstance h).initial p := by
  change tile (r, p.1.val, p.2.val) =
    Encoding.tile { walls := ∅, goals := (holes r.width r.height r.targetSegments)ᶜ }
      { player := (⟨r.playerX, h.playerX_lt⟩, ⟨r.playerY, h.playerY_lt⟩)
        boxes := (holes r.width r.height r.initialSegments)ᶜ } p
  simp [tile, Encoding.tile, holes, Finset.notMem_empty,
    Prod.ext_iff, Fin.ext_iff]

/-- The complete dense output is exactly the actual wall-free instance's standard data. -/
theorem data_eq (r : SegmentRecipe) (h : r.Valid) :
    Encoding.data (r.toInstance h).toInstance = emit r := by
  have hw : (r.toInstance h).width = r.width := rfl
  have hh : (r.toInstance h).height = r.height := rfl
  change Encoding.Data.mk r.width r.height (Encoding.rows _ _) =
    Encoding.Data.mk r.width r.height ((List.range r.height).map fun y =>
      (List.range r.width).map fun x => tile (r, x, y))
  congr 1
  apply List.ext_getElem
  · simp only [Encoding.rows, List.length_ofFn, List.length_map, List.length_range, hh]
  · intro y hy _
    have hy' : y < r.height := by simpa only [Encoding.rows, List.length_ofFn, hh] using hy
    simp only [Encoding.rows, List.getElem_ofFn, List.getElem_map, List.getElem_range]
    apply List.ext_getElem
    · simp only [List.length_ofFn, List.length_map, List.length_range, hw]
    · intro x hx _
      have hx' : x < r.width := by simpa only [List.length_ofFn, hw] using hx
      simp only [List.getElem_ofFn, List.getElem_map, List.getElem_range]
      exact (r.tile_eq h (⟨x, hx'⟩, ⟨y, hy'⟩)).symm

end SegmentRecipe
end PushPuzzle.PushS

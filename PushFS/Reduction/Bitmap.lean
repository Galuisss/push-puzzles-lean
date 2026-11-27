/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Encoding
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite

/-!
# Polynomial-time rasterization of placed bitmaps

Emit the full rectangle from finite tile patches with unary offsets. Walls,
boxes and goals are combined by union; a single global player coordinate
supplies the player marker. The output retains every auxiliary box and target.

## Main results

* `emit_polyTime`: an actual multi-tape-machine polynomial-time certificate.
* `cell_emit`: the emitted row table agrees pointwise with the patch union.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.Bitmap


open Turing.MultiTapeTM ComputableInPolyTime
open scoped Encoding

/-- One finite tile with its unary translation. -/
structure Patch where
  /-- Horizontal offset. -/
  x : ℕ
  /-- Vertical offset. -/
  y : ℕ
  /-- Dense local tile bitmap. -/
  bitmap : Encoding.Data

/-- The target rectangle, one player and all translated finite tiles. -/
structure Input where
  /-- Output width. -/
  width : ℕ
  /-- Output height. -/
  height : ℕ
  /-- Global player's horizontal coordinate. -/
  playerX : ℕ
  /-- Global player's vertical coordinate. -/
  playerY : ℕ
  /-- Tile patches, allowing overlapping wall collars. -/
  patches : List Patch

/-- Unary offsets followed by the dense local bitmap. -/
enc_structure encPatch : Patch where
  x : encUnary, y : encUnary, bitmap : Encoding.encData

/-- Unary dimensions and player coordinates followed by the framed patch list. -/
enc_structure encInput : Input where
  width : encUnary, height : encUnary, playerX : encUnary, playerY : encUnary,
  patches : (encList encPatch)

/-- Unary x and y coordinates. -/
abbrev encPoint : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

/-- A translated patch followed by the queried x and y coordinates. -/
abbrev encPatchQuery : (Patch × ℕ × ℕ) ↪ List Bool := encPair encPatch encPoint

/-- An assembly followed by the queried x and y coordinates. -/
abbrev encQuery : (Input × ℕ × ℕ) ↪ List Bool := encPair encInput encPoint

/-- An empty floor cell. -/
def emptyTile : Encoding.Tile := ⟨false, false, false, false⟩

/-- Read a tile inside its declared local rectangle; the exterior contributes no marks. -/
def localTile (q : Patch × ℕ × ℕ) : Encoding.Tile :=
  let p := q.1
  let x := q.2.1
  let y := q.2.2
  if p.x ≤ x ∧ p.y ≤ y ∧ x - p.x < p.bitmap.width ∧ y - p.y < p.bitmap.height then
    (p.bitmap.rows.getD (y - p.y) []).getD (x - p.x) emptyTile
  else emptyTile

/-- Union one selected mark over all translated patches. -/
def flag (select : Encoding.Tile → Bool) (q : Input × ℕ × ℕ) : Bool :=
  q.1.patches.any fun p => select (localTile (p, q.2.1, q.2.2))

/-- Combine all three storage marks, retaining a single global player. -/
def tile (q : Input × ℕ × ℕ) : Encoding.Tile :=
  ⟨flag Encoding.Tile.wall q, flag Encoding.Tile.goal q, flag Encoding.Tile.box q,
    decide (q.2.1 = q.1.playerX ∧ q.2.2 = q.1.playerY)⟩

/-- Emit every cell of the explicit output rectangle, including empty floor. -/
def emit (x : Input) : Encoding.Data :=
  ⟨x.width, x.height, (List.range x.height).map fun y =>
    (List.range x.width).map fun z => tile (x, z, y)⟩

@[fun_prop] theorem localTile_polyTime :
    ComputableInPolyTime localTile encPatchQuery Encoding.encTile := by
  have hrow : ComputableInPolyTime
      (fun q : List (List Encoding.Tile) × ℕ => q.1.getD q.2 [])
      (encPair (encList (encList Encoding.encTile)) encUnary) (encList Encoding.encTile) := listGetD []
  have htile : ComputableInPolyTime
      (fun q : List Encoding.Tile × ℕ => q.1.getD q.2 emptyTile)
      (encPair (encList Encoding.encTile) encUnary) Encoding.encTile := listGetD emptyTile
  unfold localTile encPatchQuery encPoint
  fun_prop

private theorem flag_polyTime (select : Encoding.Tile → Bool) :
    ComputableInPolyTime (flag select) encQuery encBool := by
  have hselect : ComputableInPolyTime select Encoding.encTile encBool := of_finite select
  unfold flag encQuery encPoint
  fun_prop

@[fun_prop] theorem tile_polyTime : ComputableInPolyTime tile encQuery Encoding.encTile := by
  have hw := flag_polyTime Encoding.Tile.wall
  have hg := flag_polyTime Encoding.Tile.goal
  have hb := flag_polyTime Encoding.Tile.box
  unfold tile encQuery encPoint
  fun_prop

/-- The full dense output, scanning and local lookups have a polynomial-time machine. -/
theorem emit_polyTime : ComputableInPolyTime emit encInput Encoding.encData := by
  unfold emit
  fun_prop

end PushPuzzle.PushFS.Reduction.Bitmap

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Run
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Structure
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.DeriveFintype
import Lean.Elab.Tactic.Omega

/-!
# Dense storage-instance encoding

Unary dimensions followed by row-major cell flags: walls, goals, boxes and player.
The encoding has length linear in the explicitly represented rectangle.
-/

@[expose] public section

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM

/-- Number of explicitly represented cells. -/
def Instance.area (I : Instance) : ℕ := I.width * I.height

theorem Instance.width_pos (I : Instance) : 0 < I.width :=
  Nat.zero_lt_of_lt I.initial.player.1.isLt

theorem Instance.height_pos (I : Instance) : 0 < I.height :=
  Nat.zero_lt_of_lt I.initial.player.2.isLt

namespace Encoding

/-- The four flags stored for each cell. -/
structure Tile where
  /-- Fixed wall marker. -/
  wall : Bool
  /-- Storage target marker. -/
  goal : Bool
  /-- Initial box marker. -/
  box : Bool
  /-- Initial player marker. -/
  player : Bool
  deriving DecidableEq, Fintype

/-- Dimensions and dense rows, without proof fields. -/
structure Data where
  /-- Unary rectangle width. -/
  width : ℕ
  /-- Unary rectangle height. -/
  height : ℕ
  /-- Explicit top-to-bottom rows. -/
  rows : List (List Tile)

variable {w h : ℕ}

/-- Inspect one cell without quotienting player positions or labelling boxes. -/
def tile (B : Board w h) (s : State w h) (p : Cell w h) : Tile :=
  ⟨decide (p ∈ B.walls), decide (p ∈ B.goals), decide (p ∈ s.boxes), decide (p = s.player)⟩

/-- Rows from top to bottom, cells within each row from left to right. -/
def rows (B : Board w h) (s : State w h) : List (List Tile) :=
  List.ofFn fun y => List.ofFn fun x => tile B s (x, y)

theorem rows_injective {B B' : Board w h} {s s' : State w h}
    (heq : rows B s = rows B' s') : B = B' ∧ s = s' := by
  have hcell (p : Cell w h) : tile B s p = tile B' s' p :=
    congrFun (List.ofFn_injective (congrFun (List.ofFn_injective heq) p.2)) p.1
  have hw : B.walls = B'.walls := by
    ext p
    simpa [tile] using congrArg Tile.wall (hcell p)
  have hg : B.goals = B'.goals := by
    ext p
    simpa [tile] using congrArg Tile.goal (hcell p)
  have hb : s.boxes = s'.boxes := by
    ext p
    simpa [tile] using congrArg Tile.box (hcell p)
  have hp : s.player = s'.player := by
    simpa [tile] using congrArg Tile.player (hcell s.player)
  exact ⟨Board.ext hw hg, State.ext hp hb⟩

/-- An instance's concrete, proof-free data. -/
def data (I : Instance) : Data := ⟨I.width, I.height, rows I.board I.initial⟩

theorem data_injective : Function.Injective data := by
  rintro ⟨w, h, B, s, hB, hs, hc⟩ ⟨w', h', B', s', hB', hs', hc'⟩ heq
  have hw : w = w' := congrArg Data.width heq
  cases hw
  have hh : h = h' := congrArg Data.height heq
  cases hh
  have hr : rows B s = rows B' s' := congrArg Data.rows heq
  obtain ⟨rfl, rfl⟩ := rows_injective hr
  rfl

/-- Flags in wall, goal, box, player order, with pair framing. -/
enc_structure encTile : Tile where
  wall : encBool, goal : encBool, box : encBool, player : encBool

/-- Unary dimensions followed by framed dense rows. -/
enc_structure encData : Data where
  width : encUnary, height : encUnary, rows : (encList (encList encTile))

@[simp] theorem length_encTile (t : Tile) : (encTile t).length = 10 := by
  simp [encTile_apply, encTileFields]

end Encoding

/-- The fixed, explicit bit-string encoding used for all complexity claims. -/
def encoding : Instance ↪ List Bool :=
  (⟨Encoding.data, Encoding.data_injective⟩ : Instance ↪ Encoding.Data).trans Encoding.encData

end PushPuzzle.PushFS

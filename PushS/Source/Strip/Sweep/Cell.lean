/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.UnitGraph
public import CslibFrontier.Computability.Complexity.Problems.NCL.Gadgets.Wire
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Crossover
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Plane

/-!
# The finite cell alphabet of the actual strip sweep

There are four possible standard source vertices with one input and two outputs, three wire
arities in either color, and one crossing in each color pair. Their implementations reuse the
certified wire and crossover families.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Cell`: the fourteen local cell kinds.
* `PushPuzzle.NCL.Strip.Sweep.Cell.expand`: their actual standard planar implementations.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Cell.expandOpenSim`: open simulation for every local replacement.
* `PushPuzzle.NCL.Strip.Sweep.Cell.expand_planar`, `.expand_standard`: standard planar output cells.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

local notation "R" => Color.red
local notation "B" => Color.blue

/-- The finite local cell kinds encountered by the actual column-major sweep. -/
inductive Cell : List Color → List Color → Type
  /-- Three blue ports, with the original first slot above. -/
  | orCell : Cell [B] [B, B]
  /-- The blue port is the incoming original slot zero. -/
  | andTop : Cell [B] [R, R]
  /-- The blue port is the outgoing original slot one. -/
  | andLeft : Cell [R] [B, R]
  /-- The blue port is the outgoing original slot two. -/
  | andRight : Cell [R] [R, B]
  /-- A local minimum of one carrier in the scan order. -/
  | cup (c : Color) : Cell [] [c, c]
  /-- One incoming and one outgoing segment of one carrier. -/
  | straight (c : Color) : Cell [c] [c]
  /-- A local maximum of one carrier in the scan order. -/
  | cap (c : Color) : Cell [c, c] []
  /-- The actual horizontal and vertical unit paths through one crossing site. -/
  | cross (c d : Color) : Cell [c, d] [d, c]

namespace Cell

open Cslib.Complexity Cslib.Complexity.NCL

/-- The actual unit-graph vertex data at one local cell. -/
@[expose] def raw : {a b : List Color} → Cell a b → Prim a b
  | _, _, .orCell | _, _, .andTop | _, _, .andLeft | _, _, .andRight => [genVertex _ _ 2]
  | _, _, .cup c | _, _, .straight c | _, _, .cap c => [genVertex _ _ c.weight]
  | _, _, .cross c d => Prim.cross c d

/-- Interpret sweep cells by their actual unit-graph vertices. -/
@[expose] def interp : Interp Cell := ⟨raw⟩

/-- The existing certified AND/OR replacement of a local sweep cell. -/
@[expose] def expand : {a b : List Color} → Cell a b → Diagram Prim a b
  | _, _, .orCell => .gen (raw .orCell)
  | _, _, .andTop => .gen (raw .andTop)
  | _, _, .andLeft => .gen (raw .andLeft)
  | _, _, .andRight => .gen (raw .andRight)
  | _, _, .cup c => Gadgets.Wire.cup c
  | _, _, .straight c => Gadgets.Wire.straight c
  | _, _, .cap c => Gadgets.Wire.cap c
  | _, _, .cross c d => Planar.Crossover.diagram c d

/-- Each local replacement preserves its actual unit-graph open interface dynamically. -/
def expandOpenSim {a b : List Color} (g : Cell a b) :
    OpenSim interp Prim.interp (.gen g) (expand g) := by
  have h := OpenSim.genOfVerts (I := interp) (I' := Prim.interp) g (raw g) rfl
  cases g with
  | orCell | andTop | andLeft | andRight => exact h
  | cup c => exact h.trans (Gadgets.Wire.cupOpenSim c)
  | straight c => exact h.trans (Gadgets.Wire.straightOpenSim c)
  | cap c => exact h.trans (Gadgets.Wire.capOpenSim c)
  | cross c d => exact h.trans (Planar.Crossover.openSim c d)

/-- The actual local standard implementations have no structural crossings. -/
theorem expand_planar {a b : List Color} (g : Cell a b) : (expand g).Planar := by
  cases g with
  | orCell | andTop | andLeft | andRight => trivial
  | cup c => exact Gadgets.Wire.cup_planar c
  | straight c => exact Gadgets.Wire.straight_planar c
  | cap c => exact Gadgets.Wire.cap_planar c
  | cross c d => exact Planar.Crossover.planar c d

/-- Every implemented primitive cell is one standard AND/OR vertex. -/
theorem expand_standard {a b : List Color} (g : Cell a b) :
    (expand g).checkGens (fun p => (p.length == 1) && Prim.checkStandard p) = true := by
  cases g with
  | orCell | andTop | andLeft | andRight => decide +kernel
  | cup c => exact Gadgets.Wire.cup_checkStandard c
  | straight c => exact Gadgets.Wire.straight_checkStandard c
  | cap c => exact Gadgets.Wire.cap_checkStandard c
  | cross c d =>
    rw [expand, checkGens_and, Planar.Crossover.checkSingle, Planar.Crossover.checkStandard]
    rfl

/-- The local planar replacement emits an actual word of standard single-vertex layers. -/
private theorem expand_checkPlane {a b : List Color} (g : Cell a b) (k : ℕ) :
    ((expand g).toWord Prim.interp k).checkPlane = true :=
  checkPlane_toWord _ _ (expand_planar g) (expand_standard g)

/-- A local cell with its two explicit colored interfaces. -/
structure Fragment where
  /-- Ordered input colors. -/
  inputs : List Color
  /-- Ordered output colors. -/
  outputs : List Color
  /-- The actual local cell on those interfaces. -/
  generator : Cell inputs outputs

/-- Select the four standard source kinds from the original three slot colors. -/
@[expose] def sourceColors : Color → Color → Color → Fragment
  | B, R, R => ⟨[B], [R, R], .andTop⟩
  | R, B, R => ⟨[R], [B, R], .andLeft⟩
  | R, R, B => ⟨[R], [R, B], .andRight⟩
  | _, _, _ => ⟨[B], [B, B], .orCell⟩

/-- A standard original source weight pattern retains its actual ordered slot colors. -/
theorem sourceColors_spec (c₀ c₁ c₂ : Color)
    (h : [c₀.weight, c₁.weight, c₂.weight] ∈
      ([[1, 1, 2], [1, 2, 1], [2, 1, 1], [2, 2, 2]] : List (List ℕ))) :
    (sourceColors c₀ c₁ c₂).inputs = [c₀] ∧
      (sourceColors c₀ c₁ c₂).outputs = [c₁, c₂] := by
  cases c₀ <;> cases c₁ <;> cases c₂ <;> simp_all [sourceColors, Color.weight]

/-- Source selection emits the single threshold-two vertex on the selected original slot colors.
-/
theorem sourceColors_raw (c₀ c₁ c₂ : Color) :
    raw (sourceColors c₀ c₁ c₂).generator =
      [genVertex (sourceColors c₀ c₁ c₂).inputs (sourceColors c₀ c₁ c₂).outputs 2] := by
  cases c₀ <;> cases c₁ <;> cases c₂ <;> rfl

namespace Fragment

open Cslib.Complexity Cslib.Complexity.NCL

/-- The actual expanded word for one selected cell at a wire offset. -/
@[expose] def word (g : Fragment) (k : ℕ) : Word := (expand g.generator).toWord Prim.interp k

/-- Every selected fragment emits a word of standard plane cells. -/
theorem checkPlane_word (g : Fragment) (k : ℕ) : (g.word k).checkPlane = true :=
  expand_checkPlane g.generator k

end Fragment
end Cell
end PushPuzzle.NCL.Strip.Sweep

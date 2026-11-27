/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Cell.Resources
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Word.Fixed

/-!
# Finite instruction codes for the actual strip cells

The existing fourteen-cell alphabet is the actual fixed fragment table. Each selected dependent
fragment has a computable finite code, and decoding that code returns the same fragment.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Cell.Fragment.code`: finite index in the existing actual cell alphabet.
* `PushPuzzle.NCL.Strip.Sweep.Cell.language`: the same table as a standard encoded fixed-fragment language.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Cell.word_code`: exact agreement of decoded and original actual cell expansion.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- Finite index of the actual fragment in the existing fourteen-cell alphabet. -/
@[expose] def Fragment.code : Fragment → Fin 14
  | ⟨_, _, .orCell⟩ => 0
  | ⟨_, _, .andTop⟩ => 1
  | ⟨_, _, .andLeft⟩ => 2
  | ⟨_, _, .andRight⟩ => 3
  | ⟨_, _, .cup .red⟩ => 4
  | ⟨_, _, .cup .blue⟩ => 5
  | ⟨_, _, .straight .red⟩ => 6
  | ⟨_, _, .straight .blue⟩ => 7
  | ⟨_, _, .cap .red⟩ => 8
  | ⟨_, _, .cap .blue⟩ => 9
  | ⟨_, _, .cross .red .red⟩ => 10
  | ⟨_, _, .cross .red .blue⟩ => 11
  | ⟨_, _, .cross .blue .red⟩ => 12
  | ⟨_, _, .cross .blue .blue⟩ => 13

/-- Looking up the actual finite code recovers the same original local fragment. -/
theorem get_code (g : Fragment) : alphabet.get g.code = g := by
  rcases g with ⟨a, b, g⟩
  cases g with
  | orCell | andTop | andLeft | andRight => rfl
  | cup c | straight c | cap c => cases c <;> rfl
  | cross c d => cases c <;> cases d <;> rfl

/-- The actual fourteen-cell table, with its standard finite instruction encoding. -/
@[expose] def language : Word.Fixed.Language where
  Opcode := Fin 14
  enumeration := inferInstance
  fragment op :=
    let g := alphabet.get op
    ⟨g.inputs, g.outputs, expand g.generator⟩

/-- Decoding the selected finite code expands the same actual strip fragment. -/
theorem word_code (g : Fragment) (offset : ℕ) :
    language.word g.code offset = g.word offset := by
  change (expand (alphabet.get g.code).generator).toWord Prim.interp offset = _
  rw [get_code]
  rfl

end PushPuzzle.NCL.Strip.Sweep.Cell

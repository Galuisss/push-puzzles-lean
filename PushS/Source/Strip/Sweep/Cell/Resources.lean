/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Cell
public import PushS.Source.Strip.Sweep.Resources
public import PushS.Source.Strip.Sweep.VertexLabels

/-!
# Constant resources of the actual finite cell alphabet

Sum the actual resources of the fourteen fixed local implementations. The result is a single
constant bounding both the emitted layer count and the newly created wires of every local cell.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget`: a constant for the actual local implementations.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Cell.length_word_le`: actual emitted local length, at every wire offset.
* `PushPuzzle.NCL.Strip.Sweep.Cell.outputCount_word_le`: actual created local wires, at every wire offset.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

private theorem vertexList_length_toWord {a b : List Color} (D : Diagram Prim a b) (k : ℕ)
    (hp : D.Planar) (hs : D.checkGens (fun g => (g.length == 1)) = true) :
    (vertexList Prim.interp D).length = (D.toWord Prim.interp k).length := by
  induction D generalizing k with
  | gen g =>
    have h : g.length = 1 := by simpa only [checkGens, beq_iff_eq] using hs
    change g.length = 1
    exact h
  | id _ => rfl
  | swap _ _ => exact hp.elim
  | comp D D' ih₁ ih₂ | tensor D D' ih₁ ih₂ =>
    have hs' : D.checkGens (fun g => (g.length == 1)) = true ∧
        D'.checkGens (fun g => (g.length == 1)) = true := Bool.and_eq_true_iff.mp hs
    simp only [vertexList, List.length_append, List.length_map, toWord]
    rw [ih₁ _ hp.1 hs'.1, ih₂ _ hp.2 hs'.2]

/-- The actual emitted layers plus the actual newly created wires of one fixed implementation. -/
@[expose] def resourceCost {a b : List Color} (g : Cell a b) : ℕ :=
  ((expand g).toWord Prim.interp 0).length + (expand g).innerCount

/-- The actual fourteen source, wire, and crossing implementations with their colored interfaces.
-/
@[expose] def alphabet : List Fragment :=
  [⟨_, _, .orCell⟩, ⟨_, _, .andTop⟩, ⟨_, _, .andLeft⟩, ⟨_, _, .andRight⟩,
    ⟨_, _, .cup .red⟩, ⟨_, _, .cup .blue⟩, ⟨_, _, .straight .red⟩, ⟨_, _, .straight .blue⟩,
    ⟨_, _, .cap .red⟩, ⟨_, _, .cap .blue⟩, ⟨_, _, .cross .red .red⟩, ⟨_, _, .cross .red .blue⟩,
    ⟨_, _, .cross .blue .red⟩, ⟨_, _, .cross .blue .blue⟩]

/-- A fixed budget for the actual layer and wire resources of all fourteen local implementations.
-/
@[expose] def expansionBudget : ℕ :=
  1 + (alphabet.map (fun g => resourceCost g.generator)).sum

private theorem cost_le {a b : List Color} (g : Cell a b) : resourceCost g ≤ expansionBudget := by
  have hg : (⟨a, b, g⟩ : Fragment) ∈ alphabet := by
    cases g with
    | orCell | andTop | andLeft | andRight => simp [alphabet]
    | cup c | straight c | cap c => cases c <;> simp [alphabet]
    | cross c d => cases c <;> cases d <;> simp [alphabet]
  have hmem : resourceCost g ∈ alphabet.map (fun f => resourceCost f.generator) :=
    List.mem_map.mpr ⟨⟨a, b, g⟩, hg, rfl⟩
  change resourceCost g ≤ 1 + (alphabet.map (fun f => resourceCost f.generator)).sum
  have hs : resourceCost g ≤ (alphabet.map (fun f => resourceCost f.generator)).sum :=
    List.le_sum_of_mem hmem
  have hn := Nat.le_add_left (alphabet.map (fun f => resourceCost f.generator)).sum 1
  exact hs.trans hn

/-- The actual emitted cell word has fixed length at every surrounding wire offset. -/
theorem length_word_le {a b : List Color} (g : Cell a b) (k : ℕ) :
    ((expand g).toWord Prim.interp k).length ≤ expansionBudget := by
  rw [length_toWord_offset Prim.interp _ k 0]
  exact (Nat.le_add_right _ _).trans (cost_le g)

/-- Every local implementation creates at most the fixed actual wire budget. -/
theorem outputCount_word_le {a b : List Color} (g : Cell a b) (k : ℕ) :
    (PushPuzzle.NCL.Word.outputCount ((expand g).toWord Prim.interp k)) ≤ expansionBudget := by
  rw [outputCount_toWord]
  exact (Nat.le_add_left _ _).trans (cost_le g)

/-- Every actual local implementation emits at most the fixed budget of actual vertices. -/
theorem vertexCount_le {a b : List Color} (g : Cell a b) :
    (vertexList Prim.interp (expand g)).length ≤ expansionBudget := by
  have hs := expand_standard g
  rw [checkGens_and] at hs
  rw [vertexList_length_toWord _ 0 (expand_planar g) (Bool.and_eq_true_iff.mp hs).1]
  exact length_word_le g 0

end PushPuzzle.NCL.Strip.Sweep.Cell

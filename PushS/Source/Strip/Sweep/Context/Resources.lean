/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Diagram
public import PushS.Source.Strip.Sweep.Cell.Resources

/-!
# Constant stack width of the actual emitted strip program

Each actual scan step begins at the already bounded original unit-arc frontier. Its fixed local
implementation creates only a constant number of extra wires. These actual checked interfaces
reset the local budget at every step, giving a uniform stack bound for the whole emitted program.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.widthBudget`: actual frontier capacity plus the fixed local expansion budget.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.program_widthBound`: every actual program prefix has bounded stack width.
* `PushPuzzle.NCL.Strip.Sweep.Context.program_length_le`: fixed emitted work per actual scan position.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Original actual frontier capacity plus the fixed cell expansion's created-wire budget. -/
@[expose] def widthBudget (K : ℕ) : ℕ := 4 * K + 10 + PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget

namespace Context

open Cslib.Complexity Cslib.Complexity.NCL

variable {A K : ℕ} (C : Context A K)

/-- Every actual original colored frontier has the derived fixed-track capacity. -/
private theorem frontierColors_length_le (t : ℤ) : (C.frontierColors t).length ≤ 4 * K + 10 := by
  simpa only [frontierColors, List.length_map] using
    frontier_length_le C.environment (List.nodup_finRange _) t

private theorem stepWord_outputCount_le (p : Cslib.Orthogonal.Point) :
    (PushPuzzle.NCL.Word.outputCount (stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p)) ≤ PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := by
  unfold stepWord instruction
  cases hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p with
  | none => simp [PushPuzzle.NCL.Word.outputCount]
  | some site =>
    simpa only [Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, PushPuzzle.NCL.Strip.Sweep.Cell.Fragment.word] using
        PushPuzzle.NCL.Strip.Sweep.Cell.outputCount_word_le (site.fragment C.graph C.arity C.color).generator
          (slice C.environment (List.finRange C.source.edgeCount) p).above.length

private theorem stepWord_length_le (p : Cslib.Orthogonal.Point) :
    (stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p).length ≤ PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := by
  unfold stepWord instruction
  cases hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p with
  | none => simp
  | some site =>
    simpa only [Option.map_some, Option.toList_some, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, PushPuzzle.NCL.Strip.Sweep.Cell.Fragment.word] using
        PushPuzzle.NCL.Strip.Sweep.Cell.length_word_le (site.fragment C.graph C.arity C.color).generator
          (slice C.environment (List.finRange C.source.edgeCount) p).above.length

private theorem stepWord_widthBound (t : ℤ) :
    (PushPuzzle.NCL.Word.WidthBound (stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t)))
        (C.frontierColors t) (widthBudget K) := by
  apply PushPuzzle.NCL.Word.WidthBound.mono (PushPuzzle.NCL.Word.widthBound_outputCount _ _)
  have hf := C.frontierColors_length_le t
  have hs := C.stepWord_outputCount_le (scanPoint K t)
  dsimp only [widthBudget]
  omega

private theorem prefix_widthBound (n : ℕ) :
    PushPuzzle.NCL.Word.WidthBound ((List.range n).flatMap (fun (i : ℕ) =>
      stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K i)))
      (C.frontierColors 0) (widthBudget K) := by
  induction n with
  | zero =>
    apply PushPuzzle.NCL.Word.WidthBound.mono (PushPuzzle.NCL.Word.widthBound_outputCount _ _)
    have h := C.frontierColors_length_le 0
    simpa only [List.range_zero, List.flatMap_nil, PushPuzzle.NCL.Word.outputCount, List.map_nil, List.sum_nil,
      Nat.add_zero, widthBudget] using h.trans (Nat.le_add_right _ _)
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    apply ih.append (C.stepWord_widthBound n)
    simpa only [C.diagramPrefix_word] using
      Diagram.wellTyped_toWord Prim.interp ((C.diagramPrefix n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand)

/-- Every checked prefix of the actual emitted program has uniformly bounded wire-stack width.
-/
theorem program_widthBound : (PushPuzzle.NCL.Word.WidthBound C.program) [] (widthBudget K) := by
  have h := C.prefix_widthBound (scanLength C.environment (List.finRange C.source.edgeCount))
  simpa only [program, Sweep.program, frontierColors, frontier_zero, List.map_nil] using h

private theorem prefix_length_le (n : ℕ) :
    ((List.range n).flatMap (fun (i : ℕ) =>
      stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K i))).length ≤ n * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, List.length_append, Nat.succ_mul]
    exact Nat.add_le_add ih (C.stepWord_length_le _)

/-- The actual emitted layer count is at most fixed work per actual scan position. -/
theorem program_length_le :
    C.program.length ≤ scanLength C.environment (List.finRange C.source.edgeCount) *
      PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget := C.prefix_length_le _

end Context
end PushPuzzle.NCL.Strip.Sweep

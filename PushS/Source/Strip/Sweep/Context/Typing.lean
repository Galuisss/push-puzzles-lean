/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.Typing

/-!
# Typing the actual standard strip program

The input and output colors of every computed local fragment are the colors of the actual unit
arcs crossing the corresponding scan cuts. Consecutive cuts therefore type the emitted program
from its empty initial frontier to its empty final frontier.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.frontierColors`: the colors on the actual scan frontier.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.stepWord_typeRun`: actual local interface matching.
* `PushPuzzle.NCL.Strip.Sweep.Context.program_wellTyped`: the actual emitted standard plane word is closed.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib

variable {A K : ℕ} (C : Context A K)

/-- The original colors of the actual unit arcs crossing one scan cut. -/
@[expose] def frontierColors (t : ℤ) : List Color :=
  (PushPuzzle.NCL.Strip.Sweep.frontier C.environment (List.finRange C.source.edgeCount) t).map (fun a => C.color a.edge)

private theorem before_colors {p : Cslib.Orthogonal.Point}
    (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    let s := slice C.environment (List.finRange C.source.edgeCount) p
    C.frontierColors (level K p) = s.above.map (fun a => C.color a.edge) ++
      s.incoming.map (fun a => C.color a.edge) ++ s.below.map (fun a => C.color a.edge) := by
  dsimp only
  rw [frontierColors, slice_before C.environment _ hp]
  simp only [List.map_append]

private theorem after_colors {p : Cslib.Orthogonal.Point}
    (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    let s := slice C.environment (List.finRange C.source.edgeCount) p
    C.frontierColors (level K p + 1) = s.above.map (fun a => C.color a.edge) ++
      s.outgoing.map (fun a => C.color a.edge) ++ s.below.map (fun a => C.color a.edge) := by
  dsimp only
  rw [frontierColors, slice_after C.environment (List.nodup_finRange _) hp]
  simp only [List.map_append]

/-- The actual local emitted word matches the actual consecutive colored frontiers. -/
theorem stepWord_typeRun (p : Cslib.Orthogonal.Point) (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    (stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p).typeRun (C.frontierColors (level K p)) =
        some (C.frontierColors (level K p + 1)) := by
  let s := slice C.environment (List.finRange C.source.edgeCount) p
  have hb := C.before_colors hp
  have ha := C.after_colors hp
  dsimp only at hb ha
  have hs := classify_spec C.environment (List.finRange C.vertices.length)
    (List.finRange C.source.edgeCount) p
  cases hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p with
  | none =>
    rw [hc] at hs
    cases hs with
    | empty _ _ hhead =>
      have hn := List.head?_eq_none_iff.mp hhead
      obtain ⟨hi, ho⟩ := List.append_eq_nil_iff.mp hn
      simp only [hi, ho, List.map_nil, List.append_nil] at hb ha
      simp only [stepWord, instruction, hc, Option.map_none, Option.toList_none,
        List.flatMap_nil, Word.typeRun, List.foldlM_nil, hb, ha]
      rfl
  | some site =>
    have hi := C.selection_interfaces (by simpa only [hc] using hs)
    rw [← hi.1] at hb
    rw [← hi.2] at ha
    let g := site.fragment C.graph C.arity C.color
    have ht := Diagram.typeRun_toWord Prim.interp (PushPuzzle.NCL.Strip.Sweep.Cell.expand g.generator)
      s.above.length (s.above.map (fun a => C.color a.edge)) (s.below.map (fun a => C.color a.edge))
      (by simp)
    simp only [stepWord, instruction, hc, Option.map_some, Option.toList_some,
      List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [hb, ha]
    exact ht

private theorem prefix_typeRun (n : ℕ) :
    Word.typeRun ((List.range n).flatMap (fun (i : ℕ) =>
      stepWord C.environment C.graph C.arity C.color
      (List.finRange C.vertices.length) (List.finRange C.source.edgeCount) (scanPoint K i)))
        (C.frontierColors 0) = some (C.frontierColors n) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.range_succ, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, Word.typeRun_append, ih, Option.bind_some]
    simpa only [level_scanPoint, Nat.cast_add, Nat.cast_one] using
      C.stepWord_typeRun (scanPoint K n) (scanPoint_band K n)

/-- The actual emitted standard plane word has matching empty initial and final interfaces. -/
theorem program_wellTyped : C.program.WellTyped [] [] := by
  have h := C.prefix_typeRun (scanLength C.environment (List.finRange C.source.edgeCount))
  simpa only [program, Sweep.program, Word.WellTyped, frontierColors, frontier_zero,
    frontier_scanLength, List.map_nil] using h

end PushPuzzle.NCL.Strip.Sweep.Context

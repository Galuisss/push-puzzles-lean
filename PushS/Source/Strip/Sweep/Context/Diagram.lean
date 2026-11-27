/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Frame
public import PushS.Source.Strip.Sweep.Births

/-!
# The actual typed diagram emitted by the strip sweep

Each computed local cell is padded by its actual unchanged frontier context. Empty sites emit
identity diagrams. The diagrams compose at the actual consecutive frontiers; local certified
substitution emits exactly the previously defined standard plane word.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.stepDiagram`: the actual local padded cell diagram.
* `PushPuzzle.NCL.Strip.Sweep.Context.diagram`: the actual closed diagram over the finite cell alphabet.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.expanded_word`: substitution emits the actual standard program exactly.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- The actual local padded cell diagram at one integer scan cut. -/
@[expose] def stepDiagram (t : ℤ) : Diagram Cell (C.frontierColors t) (C.frontierColors (t + 1)) :=
  (C.frame t).diagram

/-- Replacing the actual padded local cell emits exactly the selected local standard word. -/
private theorem stepDiagram_word (t : ℤ) :
    ((C.stepDiagram t).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 =
      stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
        (List.finRange C.source.edgeCount) (scanPoint K t) :=
  (C.frame t).word_eq

/-- The actual padded source diagrams for the first `n` scan positions. -/
@[expose] def diagramPrefix : (n : ℕ) → Diagram Cell (C.frontierColors 0) (C.frontierColors n)
  | 0 => Diagram.id (C.frontierColors 0)
  | n + 1 =>
    PushPuzzle.NCL.Strip.Sweep.Cell.retype ((diagramPrefix n).comp (C.stepDiagram n)) rfl
      (congrArg C.frontierColors (show (n : ℤ) + 1 = (n + 1 : ℕ) by omega))

/-- Replacing a computed diagram prefix emits exactly the corresponding actual program prefix. -/
theorem diagramPrefix_word (n : ℕ) :
    ((C.diagramPrefix n).subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 =
      (List.range n).flatMap (fun (i : ℕ) =>
        stepWord C.environment C.graph C.arity C.color (List.finRange C.vertices.length)
          (List.finRange C.source.edgeCount) (scanPoint K i)) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [diagramPrefix, PushPuzzle.NCL.Strip.Sweep.Cell.retype_word]
    simp only [Diagram.subst, Diagram.toWord, ih, stepDiagram_word, List.range_succ,
      List.flatMap_append, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- The actual closed finite-cell diagram assembled by the complete grid scan. -/
@[expose] def diagram : Diagram Cell [] [] :=
  PushPuzzle.NCL.Strip.Sweep.Cell.retype (C.diagramPrefix (scanLength C.environment (List.finRange C.source.edgeCount)))
    (by simp only [frontierColors, frontier_zero, List.map_nil])
    (by simp only [frontierColors, frontier_scanLength, List.map_nil])

/-- Local certified replacements emit the actual closed standard plane program exactly. -/
theorem expanded_word : (C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand).toWord Prim.interp 0 = C.program := by
  rw [diagram, PushPuzzle.NCL.Strip.Sweep.Cell.retype_word, diagramPrefix_word]
  rfl

end PushPuzzle.NCL.Strip.Sweep.Context

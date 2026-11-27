/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.Diagram
public import CslibFrontier.Computability.Complexity.Problems.NCL.Diagram.CompileReachability

/-!
# Certified standard expansion of the actual strip diagram

Substitute the existing local wire and crossover simulations into the actual typed source diagram.
Compilation then gives precisely the emitted native finite graph, with all standard validity
properties.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.expandedDiagram`: the actual standard local replacements.
* `PushPuzzle.NCL.Strip.Sweep.Context.expansionSimulation`: full local-substitution and compilation simulation.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.program_valid`: the emitted native graph is a valid AND/OR graph.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Cell

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

/-- Expanding an actual finite-cell diagram checks as standard single-vertex primitive cells. -/
private theorem expanded_checked {a b : List Color} (D : Diagram Cell a b) :
    (D.subst expand).checkGens (fun p => (p.length == 1) && Prim.checkStandard p) = true := by
  rw [checkGens_subst]
  induction D with
  | gen g => exact expand_standard g
  | id _ | swap _ _ => rfl
  | comp _ _ ih₁ ih₂ | tensor _ _ ih₁ ih₂ =>
    simp only [checkGens, ih₁, ih₂, Bool.true_and]

end PushPuzzle.NCL.Strip.Sweep.Cell

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Diagram

variable {A K : ℕ} (C : Context A K)

/-- The actual local standard replacements in the actual closed finite-cell diagram. -/
@[expose] def expandedDiagram : Diagram Prim [] [] := C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand

/-- Every expanded generator satisfies the standard local graph and port checks. -/
private theorem expanded_checkStandard : C.expandedDiagram.checkGens Prim.checkStandard = true := by
  have h := PushPuzzle.NCL.Strip.Sweep.Cell.expanded_checked C.diagram
  simp only [checkGens_and, Bool.and_eq_true] at h
  exact h.2

/-- Actual standard expansion preserves the AND/OR kind at every output vertex. -/
private theorem expanded_isAndOr : (C.expandedDiagram.graph Prim.interp).IsAndOr :=
  isAndOr_of_checkGens Prim.interp _ ((checkGens_checkStandard_iff _).mp C.expanded_checkStandard).1

/-- The actual expanded graph has no repeated edge at a vertex. -/
private theorem expanded_loopFree : (C.expandedDiagram.graph Prim.interp).LoopFree :=
  loopFree_of_checkGens Prim.interp _
    ((checkGens_checkStandard_iff _).mp C.expanded_checkStandard).2.1

/-- Every actual expanded edge has opposite consistent weighted endpoints. -/
private theorem expanded_wellFormed : (C.expandedDiagram.graph Prim.interp).WellFormed :=
  wellFormed_of_checkGens Prim.interp _
    ((checkGens_checkStandard_iff _).mp C.expanded_checkStandard).2.2

/-- The actual emitted native finite graph is a valid standard AND/OR graph. -/
theorem program_valid : SourceValid C.program.compile := by
  have h := Diagram.compile_valid Prim.interp C.expandedDiagram C.expanded_isAndOr
    C.expanded_wellFormed
  have hl : (Word.compile (C.expandedDiagram.toWord Prim.interp 0)).graph.LoopFree := by
    rw [Diagram.compile_toWord]
    intro i
    rw [AndOrGraph.graph_ofFinite]
    exact (Diagram.finiteGraph_loopFree Prim.interp C.expandedDiagram C.expanded_loopFree) _
  have h := SourceValid.ofValid h hl
  simpa only [expandedDiagram, C.expanded_word] using h

/-- Local certified replacements and actual word compilation give one full graph simulation. -/
@[expose] def expansionSimulation :
    ConstraintGraph.Simulation (C.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp) C.program.compile.graph :=
  C.expanded_word ▸
    (substSimulation PushPuzzle.NCL.Strip.Sweep.Cell.expandOpenSim C.diagram).trans
      (compileSimulation Prim.interp (C.diagram.subst PushPuzzle.NCL.Strip.Sweep.Cell.expand))

end PushPuzzle.NCL.Strip.Sweep.Context

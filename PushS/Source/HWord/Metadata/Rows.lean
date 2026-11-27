/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.PolyTime
public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Rows
public import PushS.Source.ConstraintGraph.SelectorNetwork.Program.Rows
import all CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Metadata.Correctness
import Mathlib.Data.List.GetD

/-!
# Actual word-network row arrays in polynomial time

The same row-major graph blocks emit source-vertex and wire-owner arrays. These are the exact
row functions used by the canonical planarizer's locality and counting theorems.

## Main definitions

* `PushPuzzle.NCL.HWord.Metadata.sourceRows`: explicit source-vertex rows.
* `PushPuzzle.NCL.HWord.Metadata.ownerRows`: explicit wire-owner rows.

## Main results

* `PushPuzzle.NCL.HWord.Metadata.sourceRows_eq`, `ownerRows_eq`: actual finite-row enumeration.
* `PushPuzzle.NCL.HWord.Metadata.computableInPolyTime_sourceRows`, `computableInPolyTime_ownerRows`:
  standard polynomial-time array emission.
-/

public section

namespace PushPuzzle.NCL.HWord.Metadata

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib.Complexity.NCL.HWord.Metadata Cslib SelectorNetwork.AndOr _root_.Turing.MultiTapeTM

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Source-vertex rows in exactly the graph emitter's vertex order. -/
@[expose] def sourceRows (n : ℕ) : List ℕ := PushPuzzle.NCL.SelectorNetwork.AndOr.Program.vertexRows (blocks H hq n)

/-- Wire-owner rows in exactly the graph emitter's edge order. -/
@[expose] def ownerRows (n : ℕ) : List ℕ := PushPuzzle.NCL.SelectorNetwork.AndOr.Program.ownerRows (blocks H hq n)

/-- Source-row emission is polynomial-time in the unary word length. -/
theorem computableInPolyTime_sourceRows : ComputableInPolyTime (sourceRows H hq) encUnary
    (encList encUnary) := by
  unfold sourceRows
  simpa only [Function.comp_def] using
    (PushPuzzle.NCL.SelectorNetwork.AndOr.Program.computableInPolyTime_vertexRows (3 * q)).comp (computableInPolyTime_blocks H hq)

/-- Owner-row emission is polynomial-time in the unary word length. -/
theorem computableInPolyTime_ownerRows : ComputableInPolyTime (ownerRows H hq) encUnary
    (encList encUnary) := by
  unfold ownerRows
  simpa only [Function.comp_def] using
    (PushPuzzle.NCL.SelectorNetwork.AndOr.Program.computableInPolyTime_ownerRows (3 * q)).comp (computableInPolyTime_blocks H hq)

/-- The explicit source array lists the actual rows of the planarizer's source vertices. -/
theorem sourceRows_eq : sourceRows H hq n = List.ofFn (Planarized.vertexRow (n := n) H hq) := by
  rw [sourceRows, blocks_eq, PushPuzzle.NCL.SelectorNetwork.AndOr.Program.vertexRows_blocks]
  change List.ofFn (Planarized.sourceRow (n := n) H hq) = _
  exact List.ofFn_congr (List.length_ofFn (f := Planarized.finiteGraph (n := n) H hq)).symm
    (Planarized.sourceRow (n := n) H hq)

/-- The explicit owner array lists the actual rows of the planarizer's original wires. -/
theorem ownerRows_eq : ownerRows H hq n = List.ofFn (Planarized.ownerRow (n := n) H hq) := by
  rw [ownerRows, blocks_eq, PushPuzzle.NCL.SelectorNetwork.AndOr.Program.ownerRows_blocks]
  rfl

end PushPuzzle.NCL.HWord.Metadata

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.HWord.Rows
public import PushS.Source.Strip.OfConstraintGraph
public import PushS.Source.Strip.Density
public import PushS.Source.Strip.Boxes
public import PushS.Source.Strip.CarrierEvents
import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.AndOr

/-!
# Actual fixed-track carriers for the word network

The numbered standard AND/OR network has a bounded number of vertices and owned edges per row.
Its original port order supplies the three local columns. Slot scans and owner parity produce
actual six-point carriers, with complete support in two panels and uniform height.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.environment`: the actual finite word-network routing environment.

## Main results

* `PushPuzzle.NCL.HWord.Strip.support_window`: full carrier support in two consecutive owner panels.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib Cslib.Orthogonal

/-- Vertex-slot budget per source panel for a fixed word alphabet. -/
@[expose] def vertexBudget (q : ℕ) : ℕ := (1 + (q + q * q)) * (64 + 66 * q)

/-- Edge-slot budget per owner panel for a fixed word alphabet. -/
@[expose] def edgeBudget (q : ℕ) : ℕ := (1 + (q + q * q)) * (66 + 69 * q)

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- Scan the actual standard graph to construct the word network's fixed-track carriers. -/
@[expose] def environment :
    PushPuzzle.NCL.Strip.Environment (Fin (Planarized.vertices (n := n) H hq).length)
      (Fin (Planarized.width (n := n) H hq)) (vertexBudget q) (edgeBudget q) :=
  PushPuzzle.NCL.Strip.ofConstraintGraph (Planarized.vertices H hq) (Planarized.vertices_wellFormed H hq)
    (Planarized.vertices_loopFree H hq)
    (fun i => (Planarized.vertices_isAndOr H hq _ (List.get_mem _ i)).shape.1.le)
    (Planarized.vertexRow H hq) (Planarized.ownerRow H hq)
    (Planarized.vertexRow_card_le H hq) (Planarized.ownerRow_card_le H hq)
    (fun i p hp => by
      have h := Planarized.portRow_bounds H hq p.port
      rw [Planarized.portRow_of_mem H hq i p hp] at h
      exact h)

/-- Every real point of each original carrier stays in two consecutive source panels and at
uniform height, with constants depending only on the fixed alphabet. -/
theorem support_window (e : Fin (Planarized.width (n := n) H hq)) {p : ℝ × ℝ}
    (hp : p ∈ support ((environment (n := n) H hq).route e)) :
    8 * (vertexBudget q : ℝ) * Planarized.ownerRow H hq e + 2 ≤ p.1 ∧
      p.1 ≤ 8 * (vertexBudget q : ℝ) * (Planarized.ownerRow H hq e + 2) - 2 ∧
      4 ≤ p.2 ∧ p.2 ≤ 4 * (edgeBudget q : ℝ) + 8 :=
  (environment H hq).support_window e hp

end PushPuzzle.NCL.HWord.Strip

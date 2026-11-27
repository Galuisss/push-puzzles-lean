/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip
public import PushS.Source.Strip.Sweep.Context.OfFinite
public import PushS.Source.Strip.Sweep.Context.Correspondence
public import PushS.Source.Strip.Sweep.Context.Drawing

/-!
# The actual strip-sweep output of the fixed word network

Use the same explicitly numbered standard graph and its already proved source/owner row arrays.
Native serialization and the actual strip sweep preserve the complete word-reconfiguration
dynamics. The resulting same native output has the constructed full strip geometry.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.Sweep.context`: the actual native context of the numbered word network.
* `PushPuzzle.NCL.HWord.Strip.Sweep.program`: the actual emitted standard planar strip program.
* `PushPuzzle.NCL.HWord.Strip.Sweep.simulation`: the original standard word network and this same native output.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.reachable_orientation_iff`: exact original word-reconfiguration semantics.
* `PushPuzzle.NCL.HWord.Strip.Sweep.panel_drawing`: the actual source family's complete strip geometry.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib

variable {q n : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The same numbered word network and actual row metadata, as the native strip-routing input.
-/
@[expose] def context : PushPuzzle.NCL.Strip.Sweep.Context (vertexBudget q) (edgeBudget q) :=
  PushPuzzle.NCL.Strip.Sweep.Context.ofFinite (Planarized.finiteGraph (n := n) H hq)
    (SelectorNetwork.AndOr.Numbering.isAndOr _ _ _)
    (SelectorNetwork.AndOr.Numbering.wellFormed _ _ _)
    (SelectorNetwork.AndOr.Numbering.loopFree _ _ _)
    (Planarized.vertexRow H hq) (Planarized.ownerRow H hq)
    (Planarized.vertexRow_card_le H hq) (Planarized.ownerRow_card_le H hq)
    (fun i p hp => by
      have h := Planarized.portRow_bounds H hq p.port
      rw [Planarized.portRow_of_mem H hq i p hp] at h
      exact h)

/-- The actual emitted standard planar strip word for the same numbered source graph. -/
@[expose] def program : Word := (context (n := n) H hq).program

/-- The original standard word network is dynamically simulated by this same actual native output.
-/
@[expose] def simulation : ConstraintGraph.Simulation (AndOr.graph (n := n) H hq)
    (program (n := n) H hq).compile.graph :=
  ((SelectorNetwork.AndOr.Numbering.simulation (PortGraph.network H n) (AndOr.rowSection H hq)
    (PortGraph.bandwidthCertificate H).order).trans
      (AndOrGraph.ofFiniteSimulation (Planarized.finiteGraph H hq))).trans
        (context H hq).nativeSimulation

/-- One actual physical direction bit per actual native output edge for a source word. -/
@[expose] def orientation (word : Fin n → Fin q) :
    Fin (program (n := n) H hq).compile.edgeCount → Bool :=
  (simulation H hq).enc (AndOr.orientation H hq word)

/-- The actual physical source configuration is legal exactly for a compatible original word. -/
theorem legal_orientation_iff (word : Fin n → Fin q) :
    (program H hq).compile.graph.Legal (orientation H hq word) ↔ Legal H word :=
  (simulation H hq).legal_enc_iff.trans (AndOr.legal_orientation_iff H hq word)

/-- Canonical paths in the actual native strip output are exactly original word reconfiguration.
-/
theorem reachable_orientation_iff (source target : Fin n → Fin q) :
    (program H hq).compile.graph.Reachable (orientation H hq source) (orientation H hq target) ↔
      Reachable H source target :=
  (simulation H hq).reachable_enc_iff.trans (AndOr.reachable_orientation_iff H hq source target)

/-- The actual emitted native graph has its standard well-formed, loop-free AND/OR validity. -/
theorem program_valid : SourceValid (program (n := n) H hq).compile := (context H hq).program_valid

/-- The same actual native output has the complete strip support and per-panel feature budgets.
-/
theorem panel_drawing :
    let K := edgeBudget q
    let width := PushPuzzle.NCL.Strip.Sweep.drawingWidth (PushPuzzle.NCL.Strip.Sweep.widthBudget K)
    let span := PushPuzzle.NCL.Strip.Sweep.drawingSpan (PushPuzzle.NCL.Strip.Sweep.widthBudget K)
      ((PushPuzzle.NCL.Strip.Sweep.height K + 2) * PushPuzzle.NCL.Strip.Sweep.Cell.expansionBudget - 1)
    ∃ P : GridDrawing.Closed (program (n := n) H hq).compile.graph,
      Cslib.Complexity.Graph.IsPlanarOrthogonalDrawing P.incidenceGraph P.orthogonalDrawing ∧
      (∀ e, ∃ start : ℕ, ∀ p : ℝ × ℝ, p ∈ Cslib.Orthogonal.support (P.path e).unitRoute →
        0 ≤ p.1 ∧ p.1 ≤ width ∧ (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span) ∧
      (∀ panel, Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1) ∧
      (∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelVisit P panel) ≤ 6 * (width + 1)) ∧
      ∀ panel, Nat.card (PushPuzzle.NCL.GridDrawing.PanelSegment P panel) ≤ 12 * (width + 1) := by
  obtain ⟨P, _, hp⟩ := (context H hq).program_panel_drawing_data
  exact ⟨P, hp⟩

end PushPuzzle.NCL.HWord.Strip.Sweep

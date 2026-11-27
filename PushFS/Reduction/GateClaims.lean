/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PortGeometry
public import PushFS.NCL.PortClaims

/-!
# Actual weighted source constraints from asynchronous physical gate flags

The inward claims of the two input roles and the complemented output role
give precisely the AND/OR physical truth predicate, even while other edges
are in transit. Reordering source ports preserves every original weighted
constraint, and erasing finite edge bounds recovers the compiled graph.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL PushPuzzle.NCL

/-- Read the three physical flags directly from possibly asynchronous inward claims. -/
def OrderedPorts.claimSignals (p : OrderedPorts) (c : PortClaims.Claims ℕ) : Gadgets.Gates.Signals :=
  ⟨c p.left, c p.upper, !(c p.output)⟩

/-- Physical AND/OR legality is exactly the actual weighted claim constraint. -/
theorem legal_claimSignals_iff (p : OrderedPorts) (c : PortClaims.Claims ℕ) :
    Gadgets.Gates.legal p.isAND (p.claimSignals c) ↔ PortClaims.Satisfied p.vertex c := by
  cases ha : c p.left <;> cases hb : c p.upper <;> cases hc : c p.output <;>
    cases hk : p.isAND <;>
    simp [Gadgets.Gates.legal, OrderedPorts.claimSignals, OrderedPorts.vertex,
      PortClaims.Satisfied, PortClaims.inflow, Vertex.and, Vertex.or, ha, hb, hc, hk]

namespace Plan

end Plan

/-- Removing finite edge bounds retains exactly the original serialized constraints. -/
theorem graph_claims_legal_iff (g : AndOrGraph) (hb : g.Bounded) (c : PortClaims.Claims ℕ) :
    PortClaims.Legal g.graph (PortClaims.pullback Fin.val c) ↔
      ∀ v ∈ g.vertices, PortClaims.Satisfied v c := by
  have hm := g.graph_map_val hb
  change (∀ i, PortClaims.Satisfied (g.graph i) (PortClaims.pullback Fin.val c)) ↔ _
  have hv (i : Fin g.vertices.length) :
      PortClaims.Satisfied (g.graph i) (PortClaims.pullback Fin.val c) ↔
        PortClaims.Satisfied (g.vertices.get i) c := by
    have hvi := congrFun hm i
    change (g.graph i).map Fin.val = g.vertices.get i at hvi
    rw [← hvi]
    unfold PortClaims.Satisfied
    rw [PortClaims.inflow_map]
    rfl
  simp_rw [hv]
  constructor
  · intro hh v hv
    obtain ⟨i, rfl⟩ := List.get_of_mem hv
    exact hh i
  · intro hh i
    exact hh _ (List.get_mem _ i)

end PushPuzzle.PushFS.Reduction

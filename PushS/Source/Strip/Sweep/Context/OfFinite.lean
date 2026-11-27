/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context
public import CslibFrontier.Computability.Complexity.Problems.NCL.Instance.OfFinite

/-!
# Actual native routing contexts from finite standard graphs

Serialize the same finite standard graph with the existing native representation. Its interpreted
vertex list recovers the original list exactly, so the existing actual source/owner row metadata
transport to the native routing context without changing any row value.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.ofFinite`: the actual native context of a finite standard graph and rows.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- Serialize the same finite standard graph and transport its actual bounded row metadata. -/
@[expose] def ofFinite {v e A K : ℕ} (G : ConstraintGraph (Fin v) (Fin e))
    (ha : G.IsAndOr) (hw : G.WellFormed) (hl : G.LoopFree)
    (vertexRows : Fin (List.ofFn G).length → ℕ) (ownerRows : Fin e → ℕ)
    (hA : ∀ r, Fintype.card {i // vertexRows i = r} ≤ A)
    (hK : ∀ r, Fintype.card {edge // ownerRows edge = r} ≤ K)
    (hrows : ∀ i p, p ∈ ((List.ofFn G).get i).ports →
      ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1) : Context A K :=
  let S := AndOrGraph.ofFinite G
  let he : List.ofFn S.graph = List.ofFn G := AndOrGraph.ofFn_graph_ofFinite G
  let ix := finCongr (congrArg List.length he)
  { source := S
    valid := SourceValid.ofValid (AndOrGraph.ofFinite_valid G ha hw) (AndOrGraph.ofFinite_loopFree G hl)
    vertexRows := vertexRows ∘ ix
    ownerRows := ownerRows
    vertexCapacity := by
      intro r
      have hc : Fintype.card {i // vertexRows (ix i) = r} =
          Fintype.card {i // vertexRows i = r} :=
        Fintype.card_congr (ix.subtypeEquiv (q := fun i => vertexRows i = r) (fun _ => Iff.rfl))
      exact hc.trans_le (hA r)
    ownerCapacity := hK
    endpointRows := by
      intro i p hp
      have hv := List.get_of_eq he i
      rw [hv] at hp
      exact hrows (ix i) p hp }

end PushPuzzle.NCL.Strip.Sweep.Context

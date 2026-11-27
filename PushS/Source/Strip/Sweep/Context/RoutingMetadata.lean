/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.OfFinite
public import PushS.Source.Strip.PolyTime.RoutingMetadata

/-!
# Exact carrier records for the native strip context

Erase finite bounds in the same interpreted source vertex list and list the same actual row
functions. The standard-data compiler emits exactly the context's complete actual unit routes.
Native finite-graph serialization preserves all these metadata values.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.routingMetadata`: actual plain source and row records.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.unitRoutes_routingMetadata`: exact complete native carrier point arrays.
* `PushPuzzle.NCL.Strip.Sweep.Context.routingMetadata_ofFinite`: metadata preserved by native serialization.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib

variable {A K : ℕ} (C : Context A K)

/-- The same actual vertex port data and source/owner row arrays, with edge bounds erased. -/
@[expose] def routingMetadata : PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata :=
  PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite C.vertices C.vertexRows C.ownerRows

/-- The plain standard-data compiler returns the context's same complete actual unit routes. -/
theorem unitRoutes_routingMetadata :
    PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes A K C.routingMetadata = List.ofFn C.environment.unitRoute :=
  PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes_ofFinite C.vertices C.wellFormed C.loopFree
    (fun i => (C.arity i).le) C.vertexRows C.ownerRows C.vertexCapacity C.ownerCapacity
      C.endpointRows

/-- Native serialization preserves the same actual plain source and row metadata. -/
theorem routingMetadata_ofFinite {v e : ℕ} (G : ConstraintGraph (Fin v) (Fin e))
    (ha : G.IsAndOr) (hw : G.WellFormed) (hl : G.LoopFree)
    (vertexRows : Fin (List.ofFn G).length → ℕ) (ownerRows : Fin e → ℕ)
    (hA : ∀ r, Fintype.card {i // vertexRows i = r} ≤ A)
    (hK : ∀ r, Fintype.card {edge // ownerRows edge = r} ≤ K)
    (hrows : ∀ i p, p ∈ ((List.ofFn G).get i).ports →
      ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1) :
    (ofFinite G ha hw hl vertexRows ownerRows hA hK hrows).routingMetadata =
      PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite (List.ofFn G) vertexRows ownerRows := by
  apply PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ext
  · exact congrArg (List.map (Vertex.map Fin.val)) (AndOrGraph.ofFn_graph_ofFinite G)
  · change List.ofFn (vertexRows ∘ finCongr (congrArg List.length (AndOrGraph.ofFn_graph_ofFinite G))) = _
    exact (List.ofFn_congr (congrArg List.length (AndOrGraph.ofFn_graph_ofFinite G)).symm vertexRows).symm
  · rfl

end PushPuzzle.NCL.Strip.Sweep.Context

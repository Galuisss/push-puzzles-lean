/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.HWord.Strip.Sweep
public import PushS.Source.Strip.Sweep.Context.RoutingMetadata
public import PushS.Source.Strip.PolyTime.ArcData
public import PushS.Source.Strip.PolyTime.SliceData
public import PushS.Source.HWord.Metadata.Rows
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time actual strip carriers of the word network

The existing standard graph and unary source/owner arrays directly form the actual carrier
compiler input. Both this metadata and all complete actual carrier point lists are polynomial-
time in the source word length. Frontier and local slice queries retain the same actual indexed
arcs. Their values are exactly those of the same native strip context.

## Main definitions

* `PushPuzzle.NCL.HWord.Strip.Sweep.routingMetadata`: actual fixed-word-network routing input.
* `PushPuzzle.NCL.HWord.Strip.Sweep.unitRoutes`: all complete actual carrier point lists.

## Main results

* `PushPuzzle.NCL.HWord.Strip.Sweep.computableInPolyTime_unitRoutes`: standard encoded full carrier emission.
* `PushPuzzle.NCL.HWord.Strip.Sweep.unitRoutes_eq`: exact same native strip geometry.
-/

public section

namespace PushPuzzle.NCL.HWord.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.HWord Cslib _root_.Turing.MultiTapeTM

variable {q : ℕ} (H : Digraph (Fin q)) [DecidableRel H.Adj] (hq : 0 < q)

/-- The same explicit standard graph port data and unary actual source/owner row arrays. -/
@[expose] def routingMetadata (n : ℕ) : PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata where
  vertices := (AndOrGraph.ofFinite (Planarized.finiteGraph (n := n) H hq)).vertices
  vertexRows := PushPuzzle.NCL.HWord.Metadata.sourceRows H hq n
  ownerRows := PushPuzzle.NCL.HWord.Metadata.ownerRows H hq n

/-- The same actual routing metadata emit in polynomial time from the unary source length. -/
theorem computableInPolyTime_routingMetadata :
    ComputableInPolyTime (routingMetadata H hq) encUnary PushPuzzle.NCL.Strip.PolyTime.encRoutingMetadata := by
  have hv := encAndOrGraph_vertices_polyTime (Metadata.computableInPolyTime_graph H hq)
  unfold routingMetadata
  exact PushPuzzle.NCL.Strip.PolyTime.encRoutingMetadata_mk_polyTime hv
    (PushPuzzle.NCL.HWord.Metadata.computableInPolyTime_sourceRows H hq) (PushPuzzle.NCL.HWord.Metadata.computableInPolyTime_ownerRows H hq)

/-- The standard compiler input is exactly the same native strip context's actual metadata. -/
theorem routingMetadata_eq (n : ℕ) :
    routingMetadata H hq n = (context (n := n) H hq).routingMetadata := by
  have he := PushPuzzle.NCL.Strip.Sweep.Context.routingMetadata_ofFinite
    (Planarized.finiteGraph (n := n) H hq)
    (by exact SelectorNetwork.AndOr.Numbering.isAndOr _ _ _)
    (by exact SelectorNetwork.AndOr.Numbering.wellFormed _ _ _)
    (by exact SelectorNetwork.AndOr.Numbering.loopFree _ _ _)
    (Planarized.vertexRow H hq) (Planarized.ownerRow H hq)
    (Planarized.vertexRow_card_le H hq) (Planarized.ownerRow_card_le H hq)
    (fun i p hp => by
      have h := Planarized.portRow_bounds H hq p.port
      rw [Planarized.portRow_of_mem H hq i p hp] at h
      exact h)
  have h : routingMetadata H hq n = PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite
      (Planarized.vertices (n := n) H hq) (Planarized.vertexRow (n := n) H hq)
      (Planarized.ownerRow (n := n) H hq) := by
    simp only [routingMetadata, PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite,
      PushPuzzle.NCL.HWord.Metadata.sourceRows_eq, PushPuzzle.NCL.HWord.Metadata.ownerRows_eq, Planarized.vertices, AndOrGraph.ofFinite,
      List.map_ofFn, Function.comp_def]
  exact h.trans he.symm

/-- All original complete carrier traversals in their actual original-edge order. -/
@[expose] def unitRoutes (n : ℕ) : List Cslib.Orthogonal.Route :=
  PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes (vertexBudget q) (edgeBudget q)
    (routingMetadata H hq n)

/-- Emit all actual carrier point arrays in polynomial time under the standard encoding. -/
theorem computableInPolyTime_unitRoutes :
    ComputableInPolyTime (unitRoutes H hq) encUnary (encList PushPuzzle.NCL.Strip.PolyTime.encRoute) := by
  change ComputableInPolyTime (fun n => PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes
    (vertexBudget q) (edgeBudget q) (routingMetadata H hq n)) _ _
  simpa only [Function.comp_def] using
    (PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.computableInPolyTime_unitRoutes
      (vertexBudget q) (edgeBudget q)).comp (computableInPolyTime_routingMetadata H hq)

/-- The standard encoded compiler produces exactly the same native context's complete carriers.
-/
theorem unitRoutes_eq (n : ℕ) :
    unitRoutes H hq n = List.ofFn (context (n := n) H hq).environment.unitRoute := by
  rw [unitRoutes, routingMetadata_eq]
  exact (context H hq).unitRoutes_routingMetadata

end PushPuzzle.NCL.HWord.Strip.Sweep

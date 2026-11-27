/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCore
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal
public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem

/-! Native weighted ports are exactly the same indexed geometric source-dart incidences. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- The native finite edge retains exactly its original index in the standard listed drawing graph. -/
@[expose] def nativeEdgeIndex {g : NCL.AndOrGraph} (drawing : NCL.GridDrawing.Closed g.graph)
    (edge : Fin g.edgeCount) : Fin drawing.incidenceGraph.edges.length :=
  ⟨edge.val, by simpa only [NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn] using edge.isLt⟩

/-- Native false and true tags select the actual original source and target in the emitted listed graph. -/
theorem native_dart_vertex {g : NCL.AndOrGraph} (drawing : NCL.GridDrawing.Closed g.graph)
    (edge : Fin g.edgeCount) (side : Bool) :
    Graph.Dart.vertex (nativeEdgeIndex drawing edge, side) =
      if side then (drawing.target edge).val else (drawing.source edge).val := by
  change (if side then (drawing.incidenceGraph.edges.getD edge.val (0, 0)).2
    else (drawing.incidenceGraph.edges.getD edge.val (0, 0)).1) = _
  have hi : edge.val < drawing.incidenceGraph.edges.length := (nativeEdgeIndex drawing edge).isLt
  rw [List.getD_eq_getElem _ _ hi]
  simp only [NCL.GridDrawing.Closed.incidenceGraph, List.getElem_ofFn]

/-- Erasing the finite edge bound retains precisely each original weighted native port occurrence. -/
theorem native_weighted_port_iff (g : NCL.AndOrGraph) (hb : g.Bounded) (vertex : Fin g.vertices.length)
    (edge : Fin g.edgeCount) (side : Bool) (weight : ℕ) :
    (⟨⟨edge, side⟩, weight⟩ : NCL.WeightedPort (Fin g.edgeCount)) ∈ (g.graph vertex).ports ↔
      (⟨⟨edge.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈ (g.vertices.get vertex).ports := by
  have hp := congrArg NCL.Vertex.ports (congrFun (g.graph_map_val hb) vertex)
  change (g.graph vertex).ports.map (NCL.WeightedPort.map Fin.val) = (g.vertices.get vertex).ports at hp
  rw [← hp]
  constructor
  · intro h
    exact List.mem_map.mpr ⟨_, h, rfl⟩
  · intro h
    obtain ⟨port, hport, he⟩ := List.mem_map.mp h
    have hinj : Function.Injective (NCL.WeightedPort.map (Fin.val (n := g.edgeCount))) :=
      NCL.WeightedPort.map_injective Fin.val_injective
    have he' : port = (⟨⟨edge, side⟩, weight⟩ : NCL.WeightedPort (Fin g.edgeCount)) := hinj he
    exact he' ▸ hport

/-- The emitted indexed geometric dart is incident at a native vertex exactly when the same original weighted port occurs there. -/
theorem native_dart_port_iff (g : NCL.AndOrGraph) (hb : g.Bounded) (drawing : NCL.GridDrawing.Closed g.graph)
    (vertex : Fin g.vertices.length) (edge : Fin g.edgeCount) (side : Bool) :
    Graph.Dart.vertex (nativeEdgeIndex drawing edge, side) = vertex.val ↔
      ∃ weight, (⟨⟨edge.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈ (g.vertices.get vertex).ports := by
  rw [native_dart_vertex]
  cases side with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    constructor
    · intro he
      have he' : drawing.source edge = vertex := Fin.ext he
      obtain ⟨weight, hp⟩ := drawing.source_port edge
      rw [he'] at hp
      exact ⟨weight, (native_weighted_port_iff g hb vertex edge false weight).mp hp⟩
    · rintro ⟨weight, hp⟩
      exact congrArg Fin.val (drawing.source_eq vertex edge ⟨weight, (native_weighted_port_iff g hb vertex edge false weight).mpr hp⟩)
  | true =>
    simp only [ite_true]
    constructor
    · intro he
      have he' : drawing.target edge = vertex := Fin.ext he
      obtain ⟨weight, hp⟩ := drawing.target_port edge
      rw [he'] at hp
      exact ⟨weight, (native_weighted_port_iff g hb vertex edge true weight).mp hp⟩
    · rintro ⟨weight, hp⟩
      exact congrArg Fin.val (drawing.target_eq vertex edge ⟨weight, (native_weighted_port_iff g hb vertex edge true weight).mpr hp⟩)

end PushPuzzle.PushS.Comb

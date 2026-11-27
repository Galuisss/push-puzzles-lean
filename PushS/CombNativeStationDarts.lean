/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombStationDarts
public import PushS.CombNativeIncidence

/-! Native comb-tip fibers retain exactly the original compiler's weighted fan ports. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

/-- An actual native tip is incident precisely to its original weighted fan ports and its final tooth. -/
theorem native_dart_vertex_tip_iff (width height : ℕ) (g : NCL.AndOrGraph) (hb : g.Bounded)
    (drawing : NCL.GridDrawing.Closed g.graph) {d : Graph.OrthogonalDrawing}
    (hd : drawing.incidenceGraph.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (dart : Graph.Dart (augmentedGraph width hd)) (vertex : Fin d.1.length) :
    dart.vertex = stationNumber width d (.tip vertex) ↔
      (∃ (edge : Fin g.edgeCount) (side : Bool) (weight : ℕ),
        (⟨⟨edge.val, side⟩, weight⟩ : NCL.WeightedPort ℕ) ∈ fan width ⟨g, d⟩ vertex.val ∧
          dart = sourceTipDart width hd (nativeEdgeIndex drawing edge) side) ∨
        dart = toothTipDart width hd vertex := by
  have hlen : d.1.length = g.vertices.length := by
    rw [hd.vertexCount]
    simp only [NCL.GridDrawing.Closed.incidenceGraph, List.length_range]
  have hv : vertex.val < g.vertices.length := by rw [← hlen]; exact vertex.isLt
  let nativeVertex : Fin g.vertices.length := ⟨vertex.val, hv⟩
  have fan_mem (port : NCL.WeightedPort ℕ) :
      port ∈ fan width ⟨g, d⟩ vertex.val ↔ port ∈ (g.vertices.get nativeVertex).ports := by
    rw [(fan_perm width ⟨g, d⟩ vertex.val).mem_iff]
    simp only [List.getD_eq_getElem _ _ hv, List.get_eq_getElem]
    rfl
  rw [dart_vertex_tip_iff width height hd hfit]
  constructor
  · rintro (⟨native, hn, he⟩ | he)
    · let edge : Fin g.edgeCount := ⟨native.1.val, by
        simpa only [NCL.GridDrawing.Closed.incidenceGraph, List.length_ofFn] using native.1.isLt⟩
      have hedge : nativeEdgeIndex drawing edge = native.1 := Fin.ext rfl
      have hn' : native.vertex = nativeVertex.val := by
        simpa only [NCL.GridDrawing.Closed.incidenceGraph, List.getElem_range] using hn
      obtain ⟨weight, hp⟩ := (native_dart_port_iff g hb drawing nativeVertex edge native.2).mp (by
        rw [hedge]
        exact hn')
      exact Or.inl ⟨edge, native.2, weight, (fan_mem _).mpr hp, by simpa only [hedge] using he⟩
    · exact Or.inr he
  · rintro (⟨edge, side, weight, hp, he⟩ | he)
    · have hn := (native_dart_port_iff g hb drawing nativeVertex edge side).mpr ⟨weight, (fan_mem _).mp hp⟩
      refine Or.inl ⟨(nativeEdgeIndex drawing edge, side), ?_, he⟩
      simpa only [NCL.GridDrawing.Closed.incidenceGraph, List.getElem_range] using hn
    · exact Or.inr he

end PushPuzzle.PushS.Comb

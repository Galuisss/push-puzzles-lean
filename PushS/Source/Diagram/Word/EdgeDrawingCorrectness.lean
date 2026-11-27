/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.EdgeDrawingData
public import PushS.Source.Diagram.Word.DrawingCorrectness
import all PushS.Source.Strip.PolyTime.Incidence
import all PushS.Source.Diagram.Word.EdgeDrawingData

/-!
# Actual native incidences and endpoints of canonical edge windows

The native graph's original incidence scan picks the same unique endpoint as its complete
drawing. Its original native vertex index therefore reads exactly that endpoint's canonical
nonnegative grid coordinates.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.endpoint_eq`: exact original native incidence scan.
* `PushPuzzle.NCL.Word.DrawingData.EdgeInput.position_eq`: exact original native endpoint coordinates.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib

private theorem native_port_iff (g : AndOrGraph) (hg : g.Bounded)
    (i : Fin g.vertices.length) (p : Port (Fin g.edgeCount)) :
    p.map Fin.val ∈ (g.vertices.get i).ports.map WeightedPort.port ↔
      p ∈ (g.graph i).ports.map WeightedPort.port := by
  have hv := congrFun (g.graph_map_val hg) i
  change (g.graph i).map Fin.val = g.vertices.get i at hv
  rw [← hv]
  exact Strip.PolyTime.port_mem_map Fin.val Fin.val_injective _ p

private theorem endpoint_closed (g : AndOrGraph) (hg : g.Bounded)
    (P : GridDrawing.Closed g.graph) (e : Fin g.edgeCount) (dir : Bool) :
    PushPuzzle.NCL.Strip.PolyTime.endpointIndex g.vertices ⟨e.val, dir⟩ =
      (if dir then P.target e else P.source e).val := by
  let endpoint := if dir then P.target e else P.source e
  have hp : GridDrawing.HasPort g.graph endpoint e dir := by
    cases dir
    · exact P.source_port e
    · exact P.target_port e
  apply Strip.PolyTime.endpointIndex_eq_of_unique g.vertices ⟨e.val, dir⟩ endpoint
  · apply (native_port_iff g hg endpoint ⟨e, dir⟩).mpr
    obtain ⟨weight, hw⟩ := hp
    exact List.mem_map.mpr ⟨⟨⟨e, dir⟩, weight⟩, hw, rfl⟩
  · intro j hj
    have hport := (native_port_iff g hg j ⟨e, dir⟩).mp hj
    obtain ⟨⟨p, weight⟩, hw, hp⟩ := List.mem_map.mp hport
    change p = (⟨e, dir⟩ : Port (Fin g.edgeCount)) at hp
    subst p
    have he : GridDrawing.HasPort g.graph j e dir := ⟨weight, hw⟩
    cases dir
    · exact (P.source_eq j e he).symm
    · exact (P.target_eq j e he).symm

/-- The actual original native incidence scan returns its complete drawing's same endpoint. -/
theorem EdgeInput.endpoint_eq {w : Word} (D : w.OrthogonalDrawing [] [])
    (hg : w.compile.Bounded) (e : Fin w.compile.edgeCount) (dir : Bool) :
    (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).endpoint dir =
      (if dir then (compiled D).target e else (compiled D).source e).val :=
  endpoint_closed w.compile hg (compiled D) e dir

/-- The same original scan reads the exact original native endpoint's nonnegative grid center.
-/
theorem EdgeInput.position_eq {w : Word} (D : w.OrthogonalDrawing [] [])
    (hg : w.compile.Bounded) (e : Fin w.compile.edgeCount) (dir : Bool) :
    (PushPuzzle.NCL.Word.DrawingData.EdgeInput.mk w e.val).position dir =
      (compiled D).vertex (if dir then (compiled D).target e else (compiled D).source e) := by
  unfold PushPuzzle.NCL.Word.DrawingData.EdgeInput.position
  rw [PushPuzzle.NCL.Word.DrawingData.EdgeInput.endpoint_eq D hg e dir]
  exact compiled_gridPosition D _

end PushPuzzle.NCL.Word.DrawingData

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.VertexIndex
public import PushFS.Reduction.VertexIncidence
public import PushFS.Reduction.PortRotation
import Mathlib.Data.List.GetD

/-! The executable geometric gate table retains the original source's contiguous vertex indices. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL PushPuzzle.PushFS.Reduction

/-- A real source vertex with its physical-layout position and cyclicly normalized weighted ports. -/
structure VertexData where
  /-- Original index of the upstream compiled vertex. -/
  index : ℕ
  /-- Its actual integer point in the complete source drawing. -/
  point : GridRouting.Point
  /-- The unrotated gate's W/N/E roles, with original edge numbers and directions. -/
  ports : OrderedPorts
  /-- Actual outer source-star pattern and cyclic core matching. -/
  annulus : Fin 3 × Fin 3

/-- Unary index and coordinates followed by the normalized weighted gate data. -/
enc_structure encVertexData : VertexData where
  index : encUnary, point : Bitmap.encPoint, ports : encOrderedPorts,
  annulus : (encPair encRole encRole)

/-- Emit one actual source-layer vertex at its computed global row. -/
def Layer.vertexData (l : Layer) (y : ℕ) : VertexData :=
  ⟨l.vertexIndex, (l.vertexPoint.1, l.vertexPoint.2 + y), orderPorts l.geometricVertex,
    PortAnnulus.pattern l.instruction.data.inputs.length, portRotation l.geometricVertex⟩

/-- Place all vertices using the exact same layer heights as the actual route program. -/
def placedVertices (q : List Layer × ℕ) : List VertexData :=
  (List.range q.1.length).map fun i =>
    let l := q.1.getD i ⟨.swap 0, ⟨[], 0, []⟩⟩
    l.vertexData (q.2 + rowOffset q.1 i)

/-- The actual table from a specified source cut and row. -/
def verticesFrom (w : Word) (st : Word.State) (y : ℕ) : List VertexData :=
  placedVertices (annotateFrom w st, y)

/-- The full table used to place all gates of the closed source instance. -/
def vertexRecords (w : Word) : List VertexData := verticesFrom w ⟨[], 0, []⟩ 0

@[simp] theorem verticesFrom_nil (st : Word.State) (y : ℕ) : verticesFrom [] st y = [] := rfl

theorem verticesFrom_cons (sl : Slice) (w : Word) (st : Word.State) (y : ℕ) :
    verticesFrom (sl :: w) st y = (Layer.mk sl st).vertexData y ::
      verticesFrom w (sl.run st) (y + (Layer.mk sl st).height) := by
  simp [verticesFrom, placedVertices, annotateFrom, List.range_succ_eq_map, List.map_map,
    rowOffset, Nat.add_assoc]

@[fun_prop] theorem Layer.vertexData_polyTime :
    ComputableInPolyTime (fun q : Layer × ℕ => q.1.vertexData q.2)
      (encPair encLayer encUnary) encVertexData := by
  have ho : ComputableInPolyTime (fun l : Layer => orderPorts l.geometricVertex)
      encLayer encOrderedPorts := orderPorts_polyTime.comp Layer.geometricVertex_polyTime
  have hi : ComputableInPolyTime (fun q : Layer × ℕ => q.1.vertexIndex)
      (encPair encLayer encUnary) encUnary := by fun_prop
  have hp : ComputableInPolyTime (fun q : Layer × ℕ => (q.1.vertexPoint.1, q.1.vertexPoint.2 + q.2))
      (encPair encLayer encUnary) Bitmap.encPoint := by unfold Bitmap.encPoint; fun_prop
  have hports : ComputableInPolyTime (fun q : Layer × ℕ => orderPorts q.1.geometricVertex)
      (encPair encLayer encUnary) encOrderedPorts := ho.comp (ComputableInPolyTime.fst encLayer encUnary)
  have hannulus : ComputableInPolyTime
      (fun q : Layer × ℕ => (PortAnnulus.pattern q.1.instruction.data.inputs.length, portRotation q.1.geometricVertex))
      (encPair encLayer encUnary) (encPair encRole encRole) := by fun_prop
  unfold Layer.vertexData
  fun_prop

@[fun_prop] theorem placedVertices_polyTime :
    ComputableInPolyTime placedVertices (encPair (encList encLayer) encUnary) (encList encVertexData) := by
  unfold placedVertices
  dsimp only
  fun_prop

/-- All gate coordinates, source indices, edge names and role bits are emitted in polynomial time. -/
theorem vertexRecords_polyTime :
    ComputableInPolyTime vertexRecords encWord (encList encVertexData) := by
  have ha := annotate_polyTime
  unfold vertexRecords verticesFrom
  change ComputableInPolyTime (fun w => placedVertices (annotate w, 0)) encWord (encList encVertexData)
  fun_prop

/-- The executable table's geometric points are exactly the source vertices proved by layer composition. -/
theorem mem_vertexPoints_iff (w : Word) (st : Word.State) (y : ℕ) (p : GridRouting.Point) :
    p ∈ (verticesFrom w st y).map VertexData.point ↔ VertexPointFrom w st y p := by
  induction w generalizing st y with
  | nil =>
    constructor
    · intro hp; cases hp
    · intro hp; cases hp
  | cons sl w ih =>
    rw [verticesFrom_cons, List.map_cons, List.mem_cons]
    constructor
    · rintro (rfl | hp)
      · exact VertexPointFrom.here sl w st y
      · exact VertexPointFrom.later ((ih _ _).mp hp)
    · intro hp
      cases hp with
      | here => exact Or.inl rfl
      | later hp => exact Or.inr ((ih _ _).mpr hp)

private theorem verticesFrom_indices {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hlen : st.wires.length = a.length) (y : ℕ) :
    (verticesFrom w st y).map VertexData.index = (List.range w.length).map (fun i => st.verts.length + i) := by
  induction D generalizing st y with
  | nil a => rfl
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    rw [verticesFrom_cons, List.map_cons,
      ih (sl.run st) (drawn_after_length layer st hlen)]
    have hv := l.after_vertices_length hl
    change (sl.run st).verts.length = st.verts.length + 1 at hv
    simp only [Layer.vertexData, Layer.vertexIndex, hv, List.length_cons,
      List.range_succ_eq_map, List.map_cons, List.map_map, Nat.add_zero]
    congr 1
    apply List.map_congr_left
    intro i _
    dsimp only [Function.comp_apply]
    omega

/-- Every actual source vertex appears once, at its original contiguous source index. -/
theorem vertexRecords_indices {w : Word} (hP : w.checkPlane = true) (hT : w.WellTyped [] []) :
    (vertexRecords w).map VertexData.index = List.range (Word.compile w).vertices.length := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  rw [compiled_vertex_count hP hT]
  simpa only [vertexRecords, List.length_nil, Nat.zero_add, List.map_id'] using
    verticesFrom_indices D ⟨[], 0, []⟩ rfl 0

/-- Each emitted gate record addresses the exact actual weighted source vertex at that index. -/
theorem vertexRecord_correct {w : Word} (hw : (Word.compile w).Valid)
    (hP : w.checkPlane = true) (hT : w.WellTyped [] []) {v : VertexData}
    (hv : v ∈ vertexRecords w) :
    v.index < (Word.compile w).vertices.length ∧
      ∃ source, (Word.compile w).vertices.getD v.index ⟨[], 0⟩ = source ∧
        source.minInflow = 2 ∧ source.ports.Perm v.ports.vertex.ports := by
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
  have hi' := List.mem_range.mp hi
  let ls := annotate w
  let l := ls.getD i ⟨.swap 0, ⟨[], 0, []⟩⟩
  have hl : l ∈ annotate w := by
    change ls.getD i ⟨.swap 0, ⟨[], 0, []⟩⟩ ∈ ls
    have hi'' : i < ls.length := hi'
    rw [List.getD_eq_getElem ls ⟨.swap 0, ⟨[], 0, []⟩⟩ hi'']
    exact List.getElem_mem hi''
  have hdraw := layer_hasDrawing hP hT hl
  exact ⟨l.vertexIndex_lt hl hdraw, l.normalized_vertex_at hw hl hdraw⟩

end PushPuzzle.PushFS.Reduction.Plan

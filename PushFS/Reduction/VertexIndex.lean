/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.LayerProgram
import Mathlib.Data.List.GetD

/-! Geometric layer identities are the actual vertex indices of the upstream source compiler. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.Plan


open Cslib.Complexity.NCL Turing.MultiTapeTM ComputableInPolyTime
open scoped NCL

/-- The index where this actual source layer appends its vertex. -/
def Layer.vertexIndex (l : Layer) : ℕ := l.before.verts.length

/-- A source step appends exactly its own locally numbered emitted vertices. -/
private theorem Layer.after_vertices (l : Layer) : l.after.verts = l.before.verts ++ emitted l := by
  cases he : l.instruction <;> simp [Layer.after, emitted, he, Slice.run]

/-- A drawn three-port layer appends exactly one real source vertex. -/
theorem Layer.after_vertices_length {l : Layer} (h : l.HasDrawing) :
    l.after.verts.length = l.before.verts.length + 1 := by
  obtain ⟨v, hv, _⟩ := h.geometric_incidence
  rw [l.after_vertices, hv]
  simp only [List.length_append, List.length_singleton]

private theorem run_vertex_count {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hlen : st.wires.length = a.length) :
    (Word.run w st).verts.length = st.verts.length + w.length := by
  induction D generalizing st with
  | nil a => simp only [Word.run, List.foldl_nil, List.length_nil, Nat.add_zero]
  | @cons sl w a b c layer rest ih =>
    let l : Layer := ⟨sl, st⟩
    have hl : l.HasDrawing := ⟨a, b, layer, hlen⟩
    change (Word.run w (sl.run st)).verts.length = _
    rw [ih (sl.run st) (drawn_after_length layer st hlen)]
    have hv := l.after_vertices_length hl
    change (sl.run st).verts.length = st.verts.length + 1 at hv
    rw [hv]
    simp only [List.length_cons]
    omega

/-- Every checked plane instruction is exactly one vertex of the compiled source graph. -/
theorem compiled_vertex_count {w : Word} (hP : w.checkPlane = true) (hT : w.WellTyped [] []) :
    (Word.compile w).vertices.length = w.length := by
  obtain ⟨D⟩ := Word.orthogonalDrawing hP hT
  simpa only [Word.compile, List.length_nil, Nat.zero_add] using run_vertex_count D ⟨[], 0, []⟩ rfl

private theorem layer_lookup_in_run (w : Word) (st : Word.State) {l : Layer}
    (hl : l ∈ annotateFrom w st) {v : Vertex ℕ} (hv : emitted l = [v]) :
    l.vertexIndex < (Word.run w st).verts.length ∧
      (Word.run w st).verts.getD l.vertexIndex ⟨[], 0⟩ = v := by
  induction w generalizing st with
  | nil => cases hl
  | cons sl w ih =>
    rcases List.mem_cons.mp hl with rfl | hl
    · have hh := run_vertices (sl :: w) st
      simp only [annotateFrom, List.flatMap_cons, hv] at hh
      rw [hh]
      constructor
      · simp only [Layer.vertexIndex, List.length_append, List.length_cons]
        omega
      · simp [Layer.vertexIndex, List.getD_eq_getElem?_getD]
    · exact ih (sl.run st) hl

/-- The route layer's numeric vertex index is in the actual compiled graph's interval. -/
theorem Layer.vertexIndex_lt {w : Word} {l : Layer} (hl : l ∈ annotate w) (h : l.HasDrawing) :
    l.vertexIndex < (Word.compile w).vertices.length := by
  obtain ⟨v, hv, _⟩ := h.geometric_incidence
  exact (layer_lookup_in_run w ⟨[], 0, []⟩ hl hv).1

/-- At that real index the source stores exactly this layer's emitted weighted vertex. -/
private theorem Layer.vertex_lookup {w : Word} {l : Layer} (hl : l ∈ annotate w) {v : Vertex ℕ}
    (hv : emitted l = [v]) :
    (Word.compile w).vertices.getD l.vertexIndex ⟨[], 0⟩ = v :=
  (layer_lookup_in_run w ⟨[], 0, []⟩ hl hv).2

/-- Geometric cyclic normalization is attached to the real weighted vertex at its original source index. -/
theorem Layer.normalized_vertex_at {w : Word} (hw : (Word.compile w).Valid)
    {l : Layer} (hl : l ∈ annotate w) (h : l.HasDrawing) :
    ∃ v, (Word.compile w).vertices.getD l.vertexIndex ⟨[], 0⟩ = v ∧
      v.minInflow = 2 ∧ v.ports.Perm (orderPorts l.geometricVertex).vertex.ports := by
  obtain ⟨v, hv, hp⟩ := h.geometric_incidence
  have hm := (orderPorts_correct (emitted_isAndOr hw hl (v := v) (by rw [hv]; simp))).1
  have hg := (orderPorts_correct (l.geometric_correct hw hl h).1).2
  exact ⟨v, l.vertex_lookup hl hv, hm, hp.trans hg⟩

@[fun_prop] theorem Layer.vertexIndex_polyTime : ComputableInPolyTime Layer.vertexIndex encLayer encUnary := by
  unfold Layer.vertexIndex
  fun_prop

end PushPuzzle.PushFS.Reduction.Plan

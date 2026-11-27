/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Diagram.Word.DrawingData
public import PushS.Source.Strip.Sweep.VertexRows
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal
import Mathlib.Data.List.Range

import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Pad
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Composition

/-!
# Actual canonical drawing coordinates from the original word data

The original compiler prefix stacks recover each drawn layer's exact boundary widths.
Their emitted heights therefore agree with the existing drawing's complete chronological list.

## Main results

* `PushPuzzle.NCL.Word.DrawingData.heights_eq`: exact original layer-height serialization.
-/

public section

namespace PushPuzzle.NCL.Word.DrawingData

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.Word Cslib Diagram

private theorem layer_wires_length {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) (st : Word.State) (hs : st.wires.length = a.length) :
    (sl.run st).wires.length = b.length := by
  rcases L with ⟨left, inputs, outputs, right, v, hsl, ha, hb, hp, layout⟩
  subst sl
  rw [ha] at hs
  rw [hb]
  simp only [Slice.run, List.length_append, List.length_take, List.length_ofFn,
    List.length_drop] at hs ⊢
  omega

private theorem layer_height {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) : L.layout.height = 2 * a.length + 2 * b.length + 6 := by
  have ha := congrArg List.length L.source_eq
  have hb := congrArg List.length L.target_eq
  simp only [GridLayout.Layer.height, List.length_append] at ha hb ⊢
  omega

private def heightsFrom (w : Word) (st : Word.State) : List ℕ :=
  (List.range w.length).map fun i =>
    2 * (Word.run (w.take i) st).wires.length +
      2 * (Word.run (w.take (i + 1)) st).wires.length + 6

private theorem heightsFrom_cons (sl : Slice) (w : Word) (st : Word.State) :
    heightsFrom (sl :: w) st =
      (2 * st.wires.length + 2 * (sl.run st).wires.length + 6) :: heightsFrom w (sl.run st) := by
  simp only [heightsFrom, List.length_cons, List.range_succ_eq_map, List.map_cons,
    List.map_map, Function.comp_def, List.take_zero, List.take_succ_cons, Word.run,
    List.foldl_nil, List.foldl_cons]

private theorem heightsFrom_eq {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hs : st.wires.length = a.length) :
    heightsFrom w st = (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D) := by
  induction D generalizing st with
  | nil => rfl
  | cons L D ih =>
    rw [heightsFrom_cons]
    change _ :: _ = L.layout.height :: (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D)
    rw [hs, layer_wires_length L st hs, layer_height L, ih _ (layer_wires_length L st hs)]

/-- Actual prefix compiler widths return the existing drawing's exact complete height list. -/
theorem heights_eq {w : Word} {b : List Color} (D : w.OrthogonalDrawing [] b) :
    heights w = (PushPuzzle.NCL.Word.OrthogonalDrawing.heights D) :=
  heightsFrom_eq D ⟨[], 0, []⟩ rfl

private def positionFrom (w : Word) (st : Word.State) (i : ℕ) : GridRouting.Point :=
  let sl := (w.getD i (.swap 0)).data
  (4 * sl.offset + GridStar.center sl.inputs.length,
    ((heightsFrom w st).take i).sum +
      2 * ((Word.run (w.take i) st).wires.length + 1) + 1)

private theorem boundary_vertex {V E : Type*} {G : ConstraintGraph V E} {m n m' n' : ℕ}
    {top : Fin m → E} {bottom : Fin n → E} (P : GridDrawing.Open G top bottom)
    (hm : m' = m) (hn : n' = n) (v : V) :
    (P.castBoundary hm hn).vertex v = P.vertex v := by
  cases hm
  cases hn
  rfl

private theorem layer_vertex {sl : Slice} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) (v : L.diagram.Vtx Prim.interp) :
    (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric L).vertex v =
      (4 * L.left.length + GridStar.center L.inputs.length, 2 * (a.length + 1) + 1) := by
  rcases L with ⟨left, inputs, outputs, right, vertex, hsl, ha, hb, hp, layout⟩
  have ha' := ha.trans (List.append_assoc left inputs right)
  have hb' := hb.trans (List.append_assoc left outputs right)
  cases ha'
  cases hb'
  change ((GridDrawing.Cell.drawing vertex hp layout).castBoundary
    (GridDrawing.Pad.boundary_length left inputs right)
    (GridDrawing.Pad.boundary_length left outputs right)).vertex () = _
  rw [boundary_vertex]
  change layout.center = _
  simp only [GridLayout.Layer.center, List.length_append]
  congr 1
  omega

private theorem positionFrom_zero {sl : Slice} {w : Word} {a b : List Color}
    (L : sl.OrthogonalDrawing a b) (st : Word.State) (hs : st.wires.length = a.length)
    (v : L.diagram.Vtx Prim.interp) : positionFrom (sl :: w) st 0 = (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric L).vertex v := by
  have hk : sl.data.offset = L.left.length := congrArg (fun s => s.data.offset) L.layer_eq
  have hi : sl.data.inputs = L.inputs := congrArg (fun s => s.data.inputs) L.layer_eq
  rw [layer_vertex L v]
  simp only [positionFrom, List.getD_cons_zero, List.take_zero, List.sum_nil,
    Word.run, List.foldl_nil, Nat.zero_add, hk, hi, hs]

private theorem positionFrom_succ (sl : Slice) (w : Word) (st : Word.State) (i : ℕ) :
    positionFrom (sl :: w) st (i + 1) =
      GridDrawing.shift (2 * st.wires.length + 2 * (sl.run st).wires.length + 6)
        (positionFrom w (sl.run st) i) := by
  simp only [positionFrom, heightsFrom_cons, List.getD_cons_succ, List.take_succ_cons,
    List.sum_cons, Word.run, List.foldl_cons, GridDrawing.shift]
  congr 1
  omega

private theorem positionFrom_vertex {w : Word} {a b : List Color}
    (D : w.OrthogonalDrawing a b) (st : Word.State) (hs : st.wires.length = a.length)
    (v : D.diagram.Vtx Prim.interp) :
    positionFrom w st ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val = (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v := by
  induction D generalizing st with
  | nil => exact v.elim
  | cons L D ih =>
    cases v with
    | inl v => exact positionFrom_zero L st hs v
    | inr v =>
      change positionFrom _ st (((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val + 1) =
        GridDrawing.shift (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric L).height ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v)
      rw [positionFrom_succ, ih _ (layer_wires_length L st hs), (PushPuzzle.NCL.Slice.OrthogonalDrawing.geometric_height L),
        layer_height, hs, layer_wires_length L st hs]

/-- The actual emitted point is the same original drawn vertex's exact integer-grid position. -/
private theorem positionAt_vertex {w : Word} {b : List Color} (D : w.OrthogonalDrawing [] b)
    (v : D.diagram.Vtx Prim.interp) :
    positionAt w ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val = GridDrawing.integerPoint ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v) := by
  have hp := positionFrom_vertex D ⟨[], 0, []⟩ rfl v
  exact congrArg GridDrawing.integerPoint hp

/-- The same original vertex center before embedding the nonnegative grid in the plane. -/
private theorem gridPositionAt_vertex {w : Word} {b : List Color} (D : w.OrthogonalDrawing [] b)
    (v : D.diagram.Vtx Prim.interp) :
    gridPositionAt w ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D) v).val = (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v :=
  positionFrom_vertex D ⟨[], 0, []⟩ rfl v

private theorem vertex_count {w : Word} {a b : List Color} (D : w.OrthogonalDrawing a b) :
    (vertexList Prim.interp D.diagram).length = w.length := by
  induction D with
  | nil => rfl
  | cons L D ih =>
    simp only [Word.OrthogonalDrawing.diagram, vertexList, List.length_append,
      List.length_map, (PushPuzzle.NCL.Slice.OrthogonalDrawing.vertexList_length L), ih, List.length_cons]
    omega

/-- The emitted vertex array is the existing complete drawing in its exact native vertex order.
-/
private theorem vertices_eq {w : Word} {b : List Color} (D : w.OrthogonalDrawing [] b) :
    vertices w = List.ofFn (fun i : Fin (vertexList Prim.interp D.diagram).length =>
      GridDrawing.integerPoint
        ((PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex ((vertexEquiv Prim.interp D.diagram).symm i))) := by
  apply List.ext_getElem
  · simp only [vertices, List.length_map, List.length_range, List.length_ofFn, vertex_count D]
  · intro i hi hj
    have hv := (vertexEquiv Prim.interp D.diagram).apply_symm_apply ⟨i, by simpa using hj⟩
    have hl := (PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer_val D) ((vertexEquiv Prim.interp D.diagram).symm ⟨i, by simpa using hj⟩)
    have he : ((PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer D)
        ((vertexEquiv Prim.interp D.diagram).symm ⟨i, by simpa using hj⟩)).val = i := by
      rw [hl, hv]
    simp only [vertices, List.getElem_map, List.getElem_range, List.getElem_ofFn]
    have hp := positionAt_vertex D ((vertexEquiv Prim.interp D.diagram).symm ⟨i, by simpa using hj⟩)
    rw [he] at hp
    exact hp

/-- Number the existing complete drawing by the original word compiler's exact native names. -/
@[expose] noncomputable def compiled {w : Word} (D : w.OrthogonalDrawing [] []) :
    GridDrawing.Closed w.compile.graph :=
  D.toWord_diagram ▸ ((compile_toWord Prim.interp D.diagram).symm ▸
    (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close).ofFinite)

/-- The original diagram edges in the original primitive word's exact native creation order. -/
@[expose] def nativeEdgeEquiv {w : Word} (D : w.OrthogonalDrawing [] []) :
    D.diagram.Edge ≃ Fin w.compile.edgeCount :=
  D.diagram.numEquiv.trans (finCongr (by
    have h := congrArg AndOrGraph.edgeCount (compile_toWord Prim.interp D.diagram)
    rw [D.toWord_diagram] at h
    exact h.symm))

/-- The original diagram vertices in the original primitive word's exact native list order. -/
@[expose] def nativeVertexEquiv {w : Word} (D : w.OrthogonalDrawing [] []) :
    D.diagram.Vtx Prim.interp ≃ Fin w.compile.vertices.length :=
  (vertexEquiv Prim.interp D.diagram).trans (finCongr (by
    have h := congrArg (fun g : AndOrGraph => g.vertices.length)
      (compile_toWord Prim.interp D.diagram)
    rw [D.toWord_diagram] at h
    simpa only [AndOrGraph.ofFinite, List.length_ofFn] using h.symm))

/-- The native edge tag keeps exactly the original diagram's creation-order number. -/
theorem nativeEdgeEquiv_val {w : Word} (D : w.OrthogonalDrawing [] [])
    (e : D.diagram.Edge) : (nativeEdgeEquiv D e).val = D.diagram.num e := by
  simp only [nativeEdgeEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast, numEquiv_val]

/-- Original native vertex/edge renaming retains precisely each weighted port incidence. -/
theorem native_hasPort_iff {w : Word} (D : w.OrthogonalDrawing [] [])
    (v : D.diagram.Vtx Prim.interp) (e : D.diagram.Edge) (dir : Bool) :
    GridDrawing.HasPort w.compile.graph (nativeVertexEquiv D v) (nativeEdgeEquiv D e) dir ↔
      GridDrawing.HasPort (D.diagram.graph Prim.interp) v e dir := by
  have number (g : AndOrGraph)
      (h : g = AndOrGraph.ofFinite (finiteGraph Prim.interp D.diagram))
      (hv : (vertexList Prim.interp D.diagram).length = g.vertices.length)
      (he : [].length + D.diagram.innerCount = g.edgeCount) :
      GridDrawing.HasPort g.graph
        (((vertexEquiv Prim.interp D.diagram).trans (finCongr hv)) v)
        ((D.diagram.numEquiv.trans (finCongr he)) e) dir ↔
      GridDrawing.HasPort (D.diagram.graph Prim.interp) v e dir := by
    cases h
    simp only [Equiv.trans_apply, finCongr_apply, GridDrawing.HasPort,
      AndOrGraph.graph_ofFinite, Fin.cast_cast, Fin.cast_eq_self]
    change GridDrawing.HasPort (finiteGraph Prim.interp D.diagram)
      (vertexEquiv Prim.interp D.diagram v) (D.diagram.numEquiv e) dir ↔
        GridDrawing.HasPort (D.diagram.graph Prim.interp) v e dir
    simpa only [Equiv.symm_apply_apply] using
      GridDrawing.hasPort_finiteGraph D.diagram (vertexEquiv Prim.interp D.diagram v)
        (D.diagram.numEquiv e) dir
  have hc := compile_toWord Prim.interp D.diagram
  rw [D.toWord_diagram] at hc
  unfold nativeVertexEquiv nativeEdgeEquiv
  exact number w.compile hc _ _

/-- Native compilation retains exactly the emitted original vertex-coordinate array. -/
theorem compiled_vertices {w : Word} (D : w.OrthogonalDrawing [] []) :
    (compiled D).orthogonalDrawing.1 = vertices w := by
  have number (G : AndOrGraph) (h : G = AndOrGraph.ofFinite (finiteGraph Prim.interp D.diagram)) :
      let P : GridDrawing.Closed G.graph := h.symm ▸
        (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close).ofFinite
      P.orthogonalDrawing.1 = vertices w := by
    cases h
    dsimp only
    rw [vertices_eq D]
    simp only [GridDrawing.Closed.orthogonalDrawing, GridDrawing.Closed.ofFinite,
      GridDrawing.Closed.finite, GridDrawing.Closed.reindex, GridDrawing.Open.close,
      Function.comp_def]
    apply List.ext_getElem
    · simp [AndOrGraph.ofFinite]
    · intro i hi hj
      simp only [List.getElem_ofFn]
      congr 3
  have transport (u : Word) (h : D.diagram.toWord Prim.interp 0 = u) :
      let P : GridDrawing.Closed u.compile.graph := h ▸
        ((compile_toWord Prim.interp D.diagram).symm ▸
          (GridDrawing.Closed.finite D.diagram (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).close).ofFinite)
      P.orthogonalDrawing.1 = vertices u := by
    cases h
    dsimp only
    conv_rhs => rw [D.toWord_diagram]
    exact number _ (compile_toWord Prim.interp D.diagram)
  exact transport w D.toWord_diagram

/-- The actual native vertex index reads the same original nonnegative canonical center. -/
theorem compiled_gridPosition {w : Word} (D : w.OrthogonalDrawing [] [])
    (i : Fin w.compile.vertices.length) : gridPositionAt w i.val = (compiled D).vertex i := by
  have hl : w.compile.vertices.length = w.length := by
    have h := congrArg List.length (compiled_vertices D)
    simpa only [GridDrawing.Closed.orthogonalDrawing, vertices, List.length_ofFn,
      List.length_map, List.length_range] using h
  have hi : i.val < w.length := hl ▸ i.isLt
  have h := congrArg (fun r : Orthogonal.Route => r.getD i.val (0, 0)) (compiled_vertices D)
  simp only [GridDrawing.Closed.orthogonalDrawing, vertices, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, i.isLt, ↓reduceDIte, Option.getD_some, List.getElem?_map,
    List.getElem?_range, hi, Option.map_some] at h
  exact GridDrawing.integerPoint_injective h.symm

/-- The exact original native vertex renaming keeps the same actual grid position. -/
theorem compiled_vertex {w : Word} (D : w.OrthogonalDrawing [] [])
    (v : D.diagram.Vtx Prim.interp) :
    (compiled D).vertex (nativeVertexEquiv D v) = (PushPuzzle.NCL.Word.OrthogonalDrawing.geometric D).vertex v := by
  rw [← compiled_gridPosition]
  have hv : (nativeVertexEquiv D v).val = (vertexEquiv Prim.interp D.diagram v).val := by
    simp only [nativeVertexEquiv, Equiv.trans_apply, finCongr_apply, Fin.val_cast]
  rw [hv, ← (PushPuzzle.NCL.Word.OrthogonalDrawing.vertexLayer_val D)]
  exact gridPositionAt_vertex D v

end PushPuzzle.NCL.Word.DrawingData

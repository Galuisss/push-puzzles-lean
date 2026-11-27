/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.StripSource
public import PushS.CombDirectedRoutes
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal
import Mathlib.Algebra.Order.BigOperators.Group.List

/-!
# Literal drawing geometry of the actual native strip source

The standard source's closed drawing retains the same native vertex and edge orders. Its raw
routes run from their original false ports to their original true ports. Complete source windows
bound all listed horizontal coordinates, and the finite arrays give a drawing rectangle.

## Main results

* `StripSource.route_head`, `route_last`: literal original directed endpoints.
* `StripSource.drawingFits`: a rectangle for these same native arrays.
* `StripSource.mem_drawing`: the actual source geometry used by the contour compiler.
-/

public section

namespace PushPuzzle.PushS.StripSource

open Cslib.Complexity

open Cslib.Orthogonal

variable {g : NCL.AndOrGraph} (P : NCL.GridDrawing.Closed g.graph)

/-- The original native vertex labels are the dense range in their actual original order. -/
theorem native_vertices : P.incidenceGraph.vertices = List.range g.vertices.length := rfl

/-- There is exactly one actual route per original native edge. -/
theorem native_edgeCount : P.incidenceGraph.edges.length = g.edgeCount := List.length_ofFn

/-- The same native drawing has exactly one original listed position per original vertex. -/
theorem drawing_count : P.orthogonalDrawing.1.length = g.vertices.length := List.length_ofFn

private theorem native_edge (e : Fin P.incidenceGraph.edges.length) :
    P.incidenceGraph.edges[e] =
      ((P.source ⟨e.val, by simpa only [native_edgeCount] using e.isLt⟩).val,
        (P.target ⟨e.val, by simpa only [native_edgeCount] using e.isLt⟩).val) :=
  List.getElem_ofFn _

/-- Every raw route starts at its actual original false-port vertex. -/
theorem route_head (e : Fin P.incidenceGraph.edges.length) :
    (P.orthogonalDrawing.2.getD e.val []).head? =
      some (Graph.drawingPosition P.incidenceGraph P.orthogonalDrawing
        P.incidenceGraph.edges[e].1) := by
  let f : Fin g.edgeCount := ⟨e.val, by simpa only [native_edgeCount] using e.isLt⟩
  rw [native_edge P e, P.drawingPosition]
  change (P.orthogonalDrawing.2.getD f.val []).head? = _
  rw [NCL.GridDrawing.route_getD P f]
  exact (P.path f).unitRoute_head

/-- Every raw route ends at its actual original true-port vertex. -/
theorem route_last (e : Fin P.incidenceGraph.edges.length) :
    (P.orthogonalDrawing.2.getD e.val []).getLast? =
      some (Graph.drawingPosition P.incidenceGraph P.orthogonalDrawing
        P.incidenceGraph.edges[e].2) := by
  let f : Fin g.edgeCount := ⟨e.val, by simpa only [native_edgeCount] using e.isLt⟩
  rw [native_edge P e, P.drawingPosition]
  change (P.orthogonalDrawing.2.getD f.val []).getLast? = _
  rw [NCL.GridDrawing.route_getD P f]
  exact (P.path f).unitRoute_last

private theorem vertex_on_route (hg : NCL.SourceValid g) (v : Fin g.vertices.length) :
    ∃ e, NCL.GridDrawing.integerPoint (P.vertex v) ∈ (P.path e).unitRoute := by
  have hlen : 0 < (g.graph v).ports.length := by rw [(hg.isAndOr v).shape.1]; omega
  obtain ⟨pw, hpw⟩ := List.exists_mem_of_length_pos hlen
  have hi : NCL.GridDrawing.Incident g.graph v pw.1.edge := ⟨pw.1.dir, pw.2, hpw⟩
  refine ⟨pw.1.edge, ?_⟩
  rcases P.incident_iff v pw.1.edge |>.mp hi with rfl | rfl
  · exact List.mem_of_mem_head? (P.path pw.1.edge).unitRoute_head
  · exact List.mem_of_mem_getLast? (P.path pw.1.edge).unitRoute_last

/-- Complete source windows and finite actual arrays give a rectangle for the same drawing. -/
theorem drawingFits (hg : NCL.SourceValid g) {width span : ℕ}
    (hwin : ∀ e, ∃ start : ℕ, ∀ p : ℝ × ℝ,
      p ∈ support (P.path e).unitRoute → 0 ≤ p.1 ∧ p.1 ≤ width ∧
        (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span) :
    ∃ height, Graph.drawingFits P.orthogonalDrawing width height := by
  let allPoints := P.orthogonalDrawing.1 ++ P.orthogonalDrawing.2.flatten
  let height := (allPoints.map fun p => p.2.toNat).sum
  have hroute (e : Fin g.edgeCount) (p : Point) (hp : p ∈ (P.path e).unitRoute) :
      0 ≤ p.1 ∧ p.1 ≤ width ∧ 0 ≤ p.2 := by
    obtain ⟨start, hs⟩ := hwin e
    have hb := hs (realPoint p) (.inl ⟨p, hp, rfl⟩)
    dsimp only [realPoint] at hb
    obtain ⟨a, ha, _⟩ := (P.path e).unitRoute_trace p hp
    have hy : 0 ≤ p.2 := by rw [← ha]; exact Int.natCast_nonneg _
    exact ⟨by exact_mod_cast hb.1, by exact_mod_cast hb.2.1, hy⟩
  have hheight (p : Point) (hp : p ∈ allPoints) : p.2 ≤ (height : ℤ) := by
    have hm : p.2.toNat ∈ allPoints.map (fun q => q.2.toNat) := List.mem_map_of_mem hp
    have hn : p.2.toNat ≤ height := List.single_le_sum (fun _ _ => Nat.zero_le _) _ hm
    omega
  refine ⟨height, ?_, ?_⟩
  · intro p hp
    obtain ⟨v, rfl⟩ := List.mem_ofFn.mp hp
    obtain ⟨e, he⟩ := vertex_on_route P hg v
    have hb := hroute e _ he
    exact ⟨hb.1, hb.2.1, hb.2.2, hheight _ (List.mem_append_left _ hp)⟩
  · intro r hr p hp
    obtain ⟨e, rfl⟩ := List.mem_ofFn.mp hr
    have hb := hroute e p hp
    exact ⟨hb.1, hb.2.1, hb.2.2,
      hheight p (List.mem_append_right _ (List.mem_flatten.mpr ⟨_, hr, hp⟩))⟩

/-- The original valid native graph and strip drawing retain their literal arrays and routes. -/
theorem valid_drawing {width span : ℕ} {x : Instance} (hg : NCL.SourceValid x.ncl.graph)
    (hx : PushPuzzle.NCL.StripAndOrNCL.ValidDrawing width span x) :
    ∃ P : NCL.GridDrawing.Closed x.ncl.graph.graph,
      P.orthogonalDrawing = (toComb x).drawing ∧
      Graph.IsPlanarOrthogonalDrawing P.incidenceGraph (toComb x).drawing ∧
      (∃ height, Graph.drawingFits (toComb x).drawing width height) ∧
      (toComb x).drawing.1.length = (toComb x).graph.vertices.length ∧
      ∀ e : Fin P.incidenceGraph.edges.length,
        ((toComb x).drawing.2.getD e.val []).head? =
          some (Graph.drawingPosition P.incidenceGraph (toComb x).drawing
            P.incidenceGraph.edges[e].1) := by
  obtain ⟨P, he, hd, hwin, _⟩ := hx
  refine ⟨P, he, hd, ?_, ?_, ?_⟩
  all_goals dsimp only [toComb]
  · rw [← he]
    exact drawingFits P hg hwin
  · rw [← he]
    exact drawing_count P
  · rw [← he]
    exact route_head P

/-- Every accepted standard source supplies the same actual native drawing, its rectangle,
and the literal original false-to-true edge routes. -/
theorem mem_drawing {width span : ℕ} {x : Instance} (hx : x ∈ language width span) :
    ∃ P : NCL.GridDrawing.Closed x.ncl.graph.graph,
      P.orthogonalDrawing = (toComb x).drawing ∧
      Graph.IsPlanarOrthogonalDrawing P.incidenceGraph (toComb x).drawing ∧
      (∃ height, Graph.drawingFits (toComb x).drawing width height) ∧
      (toComb x).drawing.1.length = (toComb x).graph.vertices.length ∧
      ∀ e : Fin P.incidenceGraph.edges.length,
        ((toComb x).drawing.2.getD e.val []).head? =
          some (Graph.drawingPosition P.incidenceGraph (toComb x).drawing
            P.incidenceGraph.edges[e].1) :=
  valid_drawing (NCL.SourceValid.ofValid hx.1.1 hx.2.1) hx.2.2

end PushPuzzle.PushS.StripSource

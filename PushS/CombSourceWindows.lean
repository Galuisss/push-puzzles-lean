/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombFeatureBounds
public import PushS.CombUpperVisits
public import PushS.CombNativeIncidence
public import PushS.StripSourceGeometry
import all PushS.CombPartition
import all PushS.CombCrossingGeometry
import all PushS.CombPreprocess
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal

/-! Every original source-visit token stays in the same actual complete-route row window. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

variable (width : ℕ) (g : NCL.AndOrGraph) (hg : NCL.SourceValid g) (drawing : NCL.GridDrawing.Closed g.graph)

include hg in
private theorem native_tip_on_route (edge : Fin g.edgeCount) (side : Bool) (vertex : Fin g.vertices.length)
    (hblock : Token.tip edge.val side ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ vertex.val).order) :
    NCL.GridDrawing.integerPoint (drawing.vertex vertex) ∈ (drawing.path edge).unitRoute := by
  obtain ⟨port, hp, he⟩ := List.mem_map.mp ((vertexBlock_tip_mem width ⟨g, drawing.orthogonalDrawing⟩ hg vertex.isLt).mp hblock)
  have hport : port.1 = (⟨edge.val, side⟩ : NCL.Port ℕ) := by
    cases port with
    | mk p weight =>
      cases p with
      | mk e dir =>
        have h := Token.tip.inj he
        cases h.1
        cases h.2
        rfl
  have hp' : (⟨⟨edge.val, side⟩, port.2⟩ : NCL.WeightedPort ℕ) ∈ (g.vertices.get vertex).ports := by
    rw [List.getD_eq_getElem _ _ vertex.isLt] at hp
    simpa only [List.get_eq_getElem, ← hport] using hp
  have hpfin := (native_weighted_port_iff g hg.1 vertex edge side port.2).mpr hp'
  cases side with
  | false =>
    have he := drawing.source_eq vertex edge ⟨port.2, hpfin⟩
    rw [← he]
    exact List.mem_of_mem_head? (drawing.path edge).unitRoute_head
  | true =>
    have he := drawing.target_eq vertex edge ⟨port.2, hpfin⟩
    rw [← he]
    exact List.mem_of_mem_getLast? (drawing.path edge).unitRoute_last

include hg in
/-- Any actual source-visit token's original block lies in that complete edge's original row window. -/
theorem source_token_window_rows (height start span : ℕ)
    (hfit : Graph.drawingFits drawing.orthogonalDrawing width height) (edge : Fin g.edgeCount)
    (hwin : ∀ p ∈ support (drawing.path edge).unitRoute, 0 ≤ p.1 ∧ p.1 ≤ width ∧
      (start : ℝ) ≤ p.2 ∧ p.2 ≤ (start : ℝ) + span)
    (vertex : Fin g.vertices.length) {token : Token}
    (hvisit : token ∈ edgeVisits width drawing.orthogonalDrawing edge.val)
    (hblock : token ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ vertex.val).order) :
    start ≤ (drawing.vertex vertex).2 ∧ (drawing.vertex vertex).2 ≤ start + span := by
  have tip_case (side : Bool)
      (ht : Token.tip edge.val side ∈ (vertexBlock width ⟨g, drawing.orthogonalDrawing⟩ vertex.val).order) :
      start ≤ (drawing.vertex vertex).2 ∧ (drawing.vertex vertex).2 ≤ start + span := by
    have hp := native_tip_on_route width g hg drawing edge side vertex ht
    have hw := hwin _ (.inl ⟨_, hp, rfl⟩)
    dsimp only [realPoint, NCL.GridDrawing.integerPoint] at hw
    exact_mod_cast hw.2.2
  rcases (edgeVisits_mem width drawing.orthogonalDrawing edge.val token).mp hvisit with ht | ht | ⟨c, hc, he, ht⟩
  · subst token
    exact tip_case false hblock
  · subst token
    exact tip_case true hblock
  · have howner : c.vertex = vertex.val := by
      rcases ht with rfl | rfl <;> exact vertexBlock_mark_owner width ⟨g, drawing.orthogonalDrawing⟩ hblock
    have hp := crossing_location_supported width drawing.isPlanarOrthogonalDrawing hc
    rw [he, route_prepare, NCL.GridDrawing.route_getD] at hp
    have hw := support_window width start span (drawing.path edge).unitRoute hwin _ hp
    have hsite : drawing.orthogonalDrawing.1.getD vertex.val (0, 0) = NCL.GridDrawing.integerPoint (drawing.vertex vertex) :=
      List.getD_ofFn _ vertex _
    have hcol : (c.location width drawing.orthogonalDrawing).1 =
        (point width (NCL.GridDrawing.integerPoint (drawing.vertex vertex))).1 := by
      simp only [Crossing.location, howner, site_prepare, hsite]
    have hcols : 2 * (stride width : ℤ) * start ≤ (point width (NCL.GridDrawing.integerPoint (drawing.vertex vertex))).1 ∧
        (point width (NCL.GridDrawing.integerPoint (drawing.vertex vertex))).1 ≤
          2 * (stride width : ℤ) * start + (2 * (stride width : ℤ) * span + 2 * width) := by
      have hw' := hw.2.2
      change 2 * (stride width : ℝ) * start ≤ ((c.location width drawing.orthogonalDrawing).1 : ℝ) ∧
        ((c.location width drawing.orthogonalDrawing).1 : ℝ) ≤ _ at hw'
      rw [hcol] at hw'
      exact_mod_cast hw'
    have hx := hfit.1 _ (List.mem_ofFn.mpr ⟨vertex, rfl⟩)
    have hy := (point_column_window_iff width start span _ ⟨hx.1, hx.2.1⟩).mp hcols
    dsimp only [NCL.GridDrawing.integerPoint] at hy
    exact_mod_cast hy

end PushPuzzle.PushS.Comb

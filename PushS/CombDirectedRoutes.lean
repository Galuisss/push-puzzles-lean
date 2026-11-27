/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPreparedDrawing

/-! Literal false-to-true source routes retain their original indexed segments after preparation. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- The standard normalization retains an actual route supplied from its original false endpoint. -/
theorem sourceRoute_reverse_eq_raw {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    (Graph.OrthogonalDrawing.sourceRoute G d edge).reverse = d.2.getD edge [] := by
  have hdecl := hd.endpointsDeclared G.edges[edge] (List.getElem_mem edge.isLt)
  have hne := hd.loopless G.edges[edge] (List.getElem_mem edge.isLt)
  have hpos : Graph.drawingPosition G d G.edges[edge].1 ≠ Graph.drawingPosition G d G.edges[edge].2 :=
    fun he => hne (Graph.OrthogonalDrawing.drawingPosition_injOn hd hdecl.1 hdecl.2 he)
  have hn : (d.2.getD edge []).head? ≠ some (Graph.OrthogonalDrawing.sourceStart G d edge) := by
    intro h
    rw [hhead, Option.some.injEq] at h
    have hs : Graph.OrthogonalDrawing.sourceStart G d edge = Graph.drawingPosition G d G.edges[edge].2 := by
      unfold Graph.OrthogonalDrawing.sourceStart
      rw [List.getD_eq_getElem _ _ edge.isLt]
      rfl
    exact hpos (h.trans hs)
  simp only [Graph.OrthogonalDrawing.sourceRoute, hn, ite_false, List.reverse_reverse]

/-- Directed input routes retain exactly the number of original internal nodes. -/
theorem preparedRoute_bends_raw (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    (preparedRoute width hd edge).bends = (d.2.getD edge []).length - 2 := by
  change (Graph.OrthogonalDrawing.sourceRoute G d edge).reverse.length - 2 = _
  rw [sourceRoute_reverse_eq_raw hd edge hhead]

/-- Every indexed node of a directed source route is its literal original prepared point. -/
theorem preparedRoute_point_raw (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (i : Fin ((preparedRoute width hd edge).bends + 2)) :
    (preparedRoute width hd edge).point i = complexPoint (point width ((d.2.getD edge []).getD i.val (0, 0))) := by
  let r := (Graph.OrthogonalDrawing.sourceRoute G d edge).reverse
  have hi : i.val < r.length := by
    have his := i.isLt
    change i.val < r.length - 2 + 2 at his
    have hlen : 2 ≤ r.length := by
      simpa only [r, List.length_reverse] using Graph.OrthogonalDrawing.sourceRoute_length_ge_two hd edge.isLt
    omega
  have hp : (preparedRoute width hd edge).point i = complexMap width (complexPoint (r.getD i.val (0, 0))) := by
    rw [List.getD_eq_getElem _ _ hi]
    rfl
  rw [hp, complexMap_complexPoint]
  have hr : r = d.2.getD edge [] := sourceRoute_reverse_eq_raw hd edge hhead
  rw [hr]

end PushPuzzle.PushS.Comb

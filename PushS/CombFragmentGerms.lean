/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombFragments
public import PushS.PolygonalCutGerms

/-! The true native ends of actual source fragments retain their original prepared outgoing rays. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

/-- The first actual source cut is the original source route's first node. -/
theorem edgeCutNode_zero (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    edgeCutNode width hd edge 0 = 0 := by
  simp only [edgeCutNode, edgeCutNodes, List.get_eq_getElem, Fin.val_zero, List.cons_append, List.getElem_cons_zero]

/-- The last actual source cut is the original source route's final node. -/
theorem edgeCutNode_last (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    edgeCutNode width hd edge (Fin.last ((edgeCrossings width d edge).length + 1)) =
      Fin.last (((refinedDrawing width hd).route edge).bends + 1) := by
  let index := (edgeCrossings width d edge).length + 1
  have hi : index < (edgeCutNodes width hd edge).length := by rw [edgeCutNodes_length]; omega
  have hget : edgeCutNode width hd edge (Fin.last ((edgeCrossings width d edge).length + 1)) =
      (edgeCutNodes width hd edge).getD index 0 := by
    rw [List.getD_eq_getElem _ _ hi]
    rfl
  rw [hget]
  change ((0 :: (edgeCrossings width d edge).attach.map (edgeCrossingNode width hd edge)) ++
    [Fin.last (((refinedDrawing width hd).route edge).bends + 1)]).getD index 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_map, List.length_attach]; exact le_rfl)]
  simp only [List.length_cons, List.length_map, List.length_attach, index, Nat.sub_self, List.getD_cons_zero]

section Geometry

variable (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
  (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
  (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))

/-- The first actual source fragment has the exact first germ of its original refined route. -/
theorem edgeFragment_start_germ :
    (edgeFragment width height hd hfit edge hhead 0).germ false = ((refinedDrawing width hd).route edge).germ false := by
  simp only [edgeFragment, Fin.castSucc_zero, edgeCutNode_zero, PushPuzzle.Polygonal.Route.germ_subroute_start]

/-- The final actual source fragment has the exact last germ of its original refined route. -/
theorem edgeFragment_finish_germ :
    (edgeFragment width height hd hfit edge hhead (Fin.last (edgeCrossings width d edge).length)).germ true =
      ((refinedDrawing width hd).route edge).germ true := by
  simp only [edgeFragment, Fin.succ_last, edgeCutNode_last, PushPuzzle.Polygonal.Route.germ_subroute_finish]

/-- The original false native source incidence keeps its genuine prepared outgoing direction. -/
theorem edgeFragment_start_arg :
    ((edgeFragment width height hd hfit edge hhead 0).germ false).arg = ((preparedRoute width hd edge).germ false).arg := by
  rw [edgeFragment_start_germ]
  exact PushPuzzle.Polygonal.Route.arg_germ_mapAtCuts_id _ _ _ false

/-- The original true native source incidence keeps its genuine prepared outgoing direction. -/
theorem edgeFragment_finish_arg :
    ((edgeFragment width height hd hfit edge hhead (Fin.last (edgeCrossings width d edge).length)).germ true).arg =
      ((preparedRoute width hd edge).germ true).arg := by
  rw [edgeFragment_finish_germ]
  exact PushPuzzle.Polygonal.Route.arg_germ_mapAtCuts_id _ _ _ true

end Geometry
end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSourceSupport
public import PushS.CombToothStationContacts
import all PushS.CombTeeth
import all PushS.CombStations

/-! Genuine source-fragment and tooth-piece contacts retain both exact named endpoint stations. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem toothStation_height_le_tip (width height : ℕ) {d : Graph.OrthogonalDrawing}
    (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (index : Fin ((toothCrossings width d vertex).length + 2)) :
    (stationPoint width d (toothStation width d vertex index)).2 ≤ ((prepare width d).1.getD vertex (0, 0)).2 := by
  rcases toothStation_cases width d vertex (toothStation_mem width d vertex index) with he | he | ⟨hit, hc, he⟩
  · rw [he]
    change (-2 : ℤ) ≤ ((prepare width d).1.getD vertex (0, 0)).2
    have := site_height_nonneg width height hfit vertex
    omega
  · rw [he]
    exact le_rfl
  · rw [he]
    exact (crossing_below_tip width d vertex hc).le

/-- Every continuous point of an actual tooth piece lies at or below its original native tip. -/
theorem toothPiece_height_le_tip (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ((toothPiece width d vertex piece).eval i t).im ≤ (((prepare width d).1.getD vertex (0, 0)).2 : ℝ) := by
  have h := toothStation_height_le_tip width height hfit vertex piece.succ
  exact (toothPiece_height_bounds width height hd hfit vertex piece i ht).2.trans (by exact_mod_cast h)

private theorem source_tooth_contact_station (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (vertex : Fin d.1.length) (tooth : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    (j : Fin (toothPiece width d vertex tooth).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i s = (toothPiece width d vertex tooth).eval j t) :
    ∃ station : Station width d,
      (edgeFragment width height hd hfit edge hhead piece).eval i s = complexPoint (stationPoint width d station) := by
  have hx := (congrArg Complex.re he).trans (toothPiece_eval_re width d vertex tooth j t)
  have hy : ((edgeFragment width height hd hfit edge hhead piece).eval i s).im ≤
      (((prepare width d).1.getD vertex (0, 0)).2 : ℝ) := by
    rw [he]
    exact toothPiece_height_le_tip width height hd hfit vertex tooth j ht
  rcases lt_or_eq_of_le hy with hlt | heq
  · obtain ⟨c, hc, _, _, hp⟩ := crossing_exists_below_tip width height hd hfit edge vertex
      (edgeFragment_mem_raw_support width height hd hfit edge hhead piece i hs) hx hlt
    exact ⟨.crossing ⟨c, hc⟩, Complex.equivRealProdCLM.injective (hp.trans (equivRealProd_complexPoint _).symm)⟩
  · refine ⟨.tip vertex, ?_⟩
    apply Complex.ext
    · exact hx
    · exact heq

/-- A true source/tooth intersection is precisely a common endpoint of the two actual pieces. -/
theorem edgeFragment_toothPiece_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (vertex : Fin d.1.length) (tooth : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    (j : Fin (toothPiece width d vertex tooth).segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i s = (toothPiece width d vertex tooth).eval j t) :
    ∃ a b, (edgeFragment width height hd hfit edge hhead piece).AtEnd i s a ∧
      (toothPiece width d vertex tooth).AtEnd j t b ∧
      edgeStation width hd edge (if a then piece.succ else piece.castSucc) =
        toothStation width d vertex (if b then tooth.succ else tooth.castSucc) := by
  obtain ⟨station, hp⟩ := source_tooth_contact_station width height hd hfit edge hhead piece vertex tooth i j hs ht he
  obtain ⟨a, ha, hname⟩ := edgeFragment_station_contact width height hd hfit edge hhead piece i hs station hp
  obtain ⟨b, hb, hname'⟩ := toothPiece_station_contact width height hd hfit vertex tooth j ht station (he.symm.trans hp)
  exact ⟨a, b, ha, hb, hname.trans hname'.symm⟩

end PushPuzzle.PushS.Comb

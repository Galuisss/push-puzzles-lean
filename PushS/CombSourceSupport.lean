/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombEdgeStations
public import PushS.CombTeeth
import all PushS.CombCrossingGeometry

/-! Actual refined source fragments keep their full prepared support above the lower comb spine. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- Literal tooth-column refinement retains the full original prepared real source support. -/
theorem refinedDrawing_route_support (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length) :
    Complex.equivRealProdCLM '' ((refinedDrawing width hd).route edge).support =
      support ((prepare width d).2.getD edge []) := by
  have h := Cslib.Polygonal.Route.support_mapAtCuts (S := toothLevels width d)
    (c := Complex.reCLM.toLinearMap.toAffineMap) (F := id) (fun _ _ _ _ _ => rfl)
    ((preparedDrawing width hd).route edge)
  change ((refinedDrawing width hd).route edge).support = id '' ((preparedDrawing width hd).route edge).support at h
  simp only [Set.image_id] at h
  rw [h, preparedDrawing_route_support]

/-- Each retained fragment evaluation belongs to its exact original indexed raw prepared route. -/
theorem edgeFragment_mem_raw_support (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    Complex.equivRealProdCLM ((edgeFragment width height hd hfit edge hhead piece).eval i t) ∈
      support ((prepare width d).2.getD edge []) := by
  rw [← refinedDrawing_route_support width hd edge]
  exact ⟨_, edgeFragment_support_subset width height hd hfit edge hhead piece
    ((edgeFragment width height hd hfit edge hhead piece).at_mem_support i ht), rfl⟩

private theorem raw_support_height_bounds (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (edge : Fin G.edges.length) {z : ℝ × ℝ} (hz : z ∈ support ((prepare width d).2.getD edge [])) :
    0 ≤ z.2 ∧ z.2 ≤ 2 * width := by
  have hi : edge.val < d.2.length := by rw [hd.edgeCount]; exact edge.isLt
  have hbound {p : Point} (hp : p ∈ (prepare width d).2.getD edge []) : 0 ≤ p.2 ∧ p.2 ≤ 2 * width :=
    prepared_height_bounds width d (fun r hr p hp => ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩) hi hp
  rcases hz with ⟨p, hp, rfl⟩ | ⟨ab, hab, hz⟩
  · have hp' := hbound hp
    change 0 ≤ (p.2 : ℝ) ∧ (p.2 : ℝ) ≤ 2 * width
    exact_mod_cast hp'
  · have hm := List.of_mem_zip hab
    have ha := hbound hm.1
    have hb := hbound (List.mem_of_mem_tail hm.2)
    have hy := (mem_segment_bounds hz).2
    change min (ab.1.2 : ℝ) ab.2.2 ≤ z.2 ∧ z.2 ≤ max (ab.1.2 : ℝ) ab.2.2 at hy
    have ha' : (0 : ℝ) ≤ ab.1.2 ∧ (ab.1.2 : ℝ) ≤ 2 * width := by exact_mod_cast ha
    have hb' : (0 : ℝ) ≤ ab.2.2 ∧ (ab.2.2 : ℝ) ≤ 2 * width := by exact_mod_cast hb
    exact ⟨(le_min ha'.1 hb'.1).trans hy.1, hy.2.trans (max_le ha'.2 hb'.2)⟩

/-- Every continuous source-fragment point stays in the original prepared vertical strip. -/
theorem edgeFragment_height_bounds (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    0 ≤ ((edgeFragment width height hd hfit edge hhead piece).eval i t).im ∧
      ((edgeFragment width height hd hfit edge hhead piece).eval i t).im ≤ 2 * width :=
  raw_support_height_bounds width height hd hfit edge (edgeFragment_mem_raw_support width height hd hfit edge hhead piece i ht)

/-- A genuine source fragment avoids every actual lower comb foot. -/
theorem edgeFragment_ne_foot (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (vertex : Fin d.1.length) :
    (edgeFragment width height hd hfit edge hhead piece).eval i t ≠ complexPoint (stationPoint width d (.foot vertex)) := by
  intro he
  have hy := congrArg Complex.im he
  have hn := (edgeFragment_height_bounds width height hd hfit edge hhead piece i ht).1
  change ((edgeFragment width height hd hfit edge hhead piece).eval i t).im = ((-2 : ℤ) : ℝ) at hy
  norm_num at hy
  linarith

/-- Every actual named comb station on a source fragment is precisely one of its own named ends. -/
theorem edgeFragment_station_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (piece : Fin ((edgeCrossings width d edge).length + 1))
    (i : Fin (edgeFragment width height hd hfit edge hhead piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (station : Station width d)
    (he : (edgeFragment width height hd hfit edge hhead piece).eval i t = complexPoint (stationPoint width d station)) :
    ∃ side, (edgeFragment width height hd hfit edge hhead piece).AtEnd i t side ∧
      edgeStation width hd edge (if side then piece.succ else piece.castSucc) = station := by
  cases station with
  | tip vertex => exact edgeFragment_tip_contact width height hd hfit edge hhead piece i ht vertex he
  | crossing hit => exact edgeFragment_crossing_contact width height hd hfit edge hhead piece i ht hit he
  | foot vertex => exact False.elim (edgeFragment_ne_foot width height hd hfit edge hhead piece i ht vertex he)

end PushPuzzle.PushS.Comb

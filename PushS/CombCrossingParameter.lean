/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombDirectedRoutes
import all PushS.CombCrossingGeometry
import all PushS.CombPreparedDrawing
import all PushS.PolygonalCutNodes
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-! Actual crossing records retain their exact source segment and strict real parameter. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

private theorem pair_lookup (r : Route) {i : ℕ} {ab : Point × Point}
    (h : r.consecutivePairs[i]? = some ab) :
    i + 1 < r.length ∧ r.getD i (0, 0) = ab.1 ∧ r.getD (i + 1) (0, 0) = ab.2 := by
  change (r.zip r.tail)[i]? = some ab at h
  have hp := List.getElem?_zip_eq_some.mp h
  simp only [List.getElem?_tail] at hp
  refine ⟨(List.getElem?_eq_some_iff.mp hp.2).1, ?_, ?_⟩ <;>
    simp only [List.getD_eq_getElem?_getD, hp.1, hp.2, Option.getD_some]

private theorem point_route_prepare (width : ℕ) (d : Graph.OrthogonalDrawing) (edge index : ℕ) :
    ((prepare width d).2.getD edge []).getD index (0, 0) =
      point width ((d.2.getD edge []).getD index (0, 0)) := by
  rw [route_prepare]
  have hz : point width (0, 0) = (0, 0) := by simp [point]
  simpa only [hz] using List.getD_map (l := d.2.getD edge []) (d := (0, 0)) (n := index) (point width)

private theorem strict_segment_parameter {a b z : Point} (hp : realPoint z ∈ Orthogonal.segment a b)
    (hstrict : min a.1 b.1 < z.1 ∧ z.1 < max a.1 b.1) :
    ∃ t : ℝ, t ∈ Set.Ioo 0 1 ∧ AffineMap.lineMap (complexPoint a) (complexPoint b) t = complexPoint z := by
  rw [Orthogonal.segment, _root_.segment_eq_image_lineMap] at hp
  obtain ⟨t, ht, he⟩ := hp
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, AffineMap.lineMap_apply_zero] at he
    have hx' := congrArg Prod.fst he
    change (a.1 : ℝ) = (z.1 : ℝ) at hx'
    have hx : a.1 = z.1 := by exact_mod_cast hx'
    omega
  have ht1 : t ≠ 1 := by
    intro h
    rw [h, AffineMap.lineMap_apply_one] at he
    have hx' := congrArg Prod.fst he
    change (b.1 : ℝ) = (z.1 : ℝ) at hx'
    have hx : b.1 = z.1 := by exact_mod_cast hx'
    omega
  refine ⟨t, ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), lt_of_le_of_ne ht.2 ht1⟩, ?_⟩
  apply Complex.equivRealProdCLM.injective
  rw [equivRealProd_complexPoint]
  have hm := AffineMap.apply_lineMap Complex.equivRealProdCLM.toLinearMap.toAffineMap
    (complexPoint a) (complexPoint b) t
  change Complex.equivRealProdCLM (AffineMap.lineMap (complexPoint a) (complexPoint b) t) =
    AffineMap.lineMap (Complex.equivRealProdCLM (complexPoint a)) (Complex.equivRealProdCLM (complexPoint b)) t at hm
  rw [equivRealProd_complexPoint, equivRealProd_complexPoint] at hm
  exact hm.trans he

private theorem prepared_segment_points (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    {index : ℕ} {ab : Point × Point}
    (hab : ((prepare width d).2.getD edge []).consecutivePairs[index]? = some ab) :
    ∃ i : Fin (preparedRoute width hd edge).segments, i.val = index ∧
      (preparedRoute width hd edge).point i.castSucc = complexPoint ab.1 ∧
      (preparedRoute width hd edge).point i.succ = complexPoint ab.2 := by
  obtain ⟨hseg, hleft, hright⟩ := pair_lookup _ hab
  have hlen : index + 1 < (d.2.getD edge []).length := by
    simpa only [route_prepare, List.length_map] using hseg
  let i : Fin (preparedRoute width hd edge).segments := ⟨index, by
    change index < (preparedRoute width hd edge).bends + 1
    rw [preparedRoute_bends_raw width hd edge hhead]
    omega⟩
  have hl := preparedRoute_point_raw width hd edge hhead i.castSucc
  have hr := preparedRoute_point_raw width hd edge hhead i.succ
  change (preparedRoute width hd edge).point i.castSucc =
    complexPoint (point width ((d.2.getD edge []).getD index (0, 0))) at hl
  change (preparedRoute width hd edge).point i.succ =
    complexPoint (point width ((d.2.getD edge []).getD (index + 1) (0, 0))) at hr
  rw [← point_route_prepare width d edge index, hleft] at hl
  rw [← point_route_prepare width d edge (index + 1), hright] at hr
  exact ⟨i, rfl, hl, hr⟩

/-- The actual marked encounter is strictly inside its recorded original source segment. -/
theorem crossing_prepared_parameter (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    {c : Crossing} (hc : c ∈ crossings width d) (hedge : edge.val = c.edge) :
    ∃ (i : Fin (preparedRoute width hd edge).segments) (t : ℝ), i.val = c.segment ∧ t ∈ Set.Ioo 0 1 ∧
      (preparedRoute width hd edge).eval i t = complexPoint (c.location width d) := by
  obtain ⟨ab, hab, hp⟩ := crossing_location_segment width hd hc
  obtain ⟨ab', hab', hstrict⟩ := crossing_location_strict width d hc
  have habab' : ab = ab' := Option.some.inj (hab.symm.trans hab')
  subst ab'
  rw [← hedge] at hab
  obtain ⟨i, hi, hl, hr⟩ := prepared_segment_points width hd edge hhead hab
  obtain ⟨t, ht, hval⟩ := strict_segment_parameter hp hstrict
  refine ⟨i, t, hi, ht, ?_⟩
  change AffineMap.lineMap _ _ t = _
  rw [hl, hr]
  exact hval

/-- The actual source direction bit is the strict horizontal direction of its retained segment. -/
theorem crossing_prepared_direction (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    {c : Crossing} (hc : c ∈ crossings width d) (hedge : edge.val = c.edge)
    (i : Fin (preparedRoute width hd edge).segments) (hi : i.val = c.segment) :
    c.forward = true ↔ ((preparedRoute width hd edge).point i.castSucc).re <
      ((preparedRoute width hd edge).point i.succ).re := by
  obtain ⟨r, ab, _, hr, hab, _, _, _, hf⟩ := (mem_crossings_iff width d c).mp hc
  have hroute : (prepare width d).2.getD edge [] = r := by
    rw [hedge]
    simp only [List.getD_eq_getElem?_getD, hr, Option.getD_some]
  have hab' : ((prepare width d).2.getD edge []).consecutivePairs[c.segment]? = some ab := by
    simpa only [hroute] using hab
  obtain ⟨j, hj, hl, hr⟩ := prepared_segment_points width hd edge hhead hab'
  have heq : i = j := Fin.ext (hi.trans hj.symm)
  subst j
  rw [hl, hr, complexPoint_re, complexPoint_re, hf, decide_eq_true_eq]
  exact_mod_cast Iff.rfl

private theorem same_segment_parameter_lt (p : Cslib.Polygonal.Route) (i : Fin p.segments)
    {a b : Crossing} (width : ℕ) {d : Graph.OrthogonalDrawing} {s t : ℝ}
    (hne : (p.point i.castSucc).re ≠ (p.point i.succ).re)
    (hdir : a.forward = true ↔ (p.point i.castSucc).re < (p.point i.succ).re)
    (ha : p.eval i s = complexPoint (a.location width d))
    (hb : p.eval i t = complexPoint (b.location width d))
    (hcol : if a.forward then (a.location width d).1 < (b.location width d).1
      else (b.location width d).1 < (a.location width d).1) : s < t := by
  have hsa : (p.eval i s).re = ((a.location width d).1 : ℝ) := by rw [ha, complexPoint_re]
  have htb : (p.eval i t).re = ((b.location width d).1 : ℝ) := by rw [hb, complexPoint_re]
  change Complex.reCLM.toLinearMap.toAffineMap (p.eval i s) = _ at hsa
  change Complex.reCLM.toLinearMap.toAffineMap (p.eval i t) = _ at htb
  rw [PushPuzzle.Polygonal.Route.coordinate_eval] at hsa htb
  simp only [AffineMap.lineMap_apply_ring'] at hsa htb
  change s * ((p.point i.succ).re - (p.point i.castSucc).re) + (p.point i.castSucc).re = _ at hsa
  change t * ((p.point i.succ).re - (p.point i.castSucc).re) + (p.point i.castSucc).re = _ at htb
  cases hf : a.forward with
  | false =>
    have hnlt : ¬(p.point i.castSucc).re < (p.point i.succ).re :=
      fun h => Bool.noConfusion (hf.symm.trans (hdir.mpr h))
    have hcoeff : (p.point i.succ).re < (p.point i.castSucc).re := lt_of_le_of_ne (le_of_not_gt hnlt) hne.symm
    simp only [hf, Bool.false_eq_true, ite_false] at hcol
    have hreal : ((b.location width d).1 : ℝ) < ((a.location width d).1 : ℝ) := by exact_mod_cast hcol
    nlinarith
  | true =>
    have hcoeff := hdir.mp hf
    simp only [hf, ite_true] at hcol
    have hreal : ((a.location width d).1 : ℝ) < ((b.location width d).1 : ℝ) := by exact_mod_cast hcol
    nlinarith

private theorem source_parameters_lt (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    {a b : Crossing} (ha : a ∈ crossings width d) (hea : edge.val = a.edge)
    (hseg : a.segment ≤ b.segment)
    (hcol : a.segment = b.segment → if a.forward then (a.location width d).1 < (b.location width d).1
      else (b.location width d).1 < (a.location width d).1)
    (i j : Fin (preparedRoute width hd edge).segments) {s t : ℝ}
    (hi : i.val = a.segment) (hj : j.val = b.segment) (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Ioo 0 1)
    (hsa : (preparedRoute width hd edge).eval i s = complexPoint (a.location width d))
    (htb : (preparedRoute width hd edge).eval j t = complexPoint (b.location width d)) :
    (preparedRoute width hd edge).position i s < (preparedRoute width hd edge).position j t := by
  by_cases heq : a.segment = b.segment
  · have hij : j = i := Fin.ext (hj.trans (heq.symm.trans hi.symm))
    subst j
    have hst := same_segment_parameter_lt _ i width (preparedDrawing_segment_nonvertical width hd edge i)
      (crossing_prepared_direction width hd edge hhead ha hea i hi) hsa htb (hcol heq)
    dsimp only [Cslib.Polygonal.Route.position]
    linarith
  · have hij : i.val + 1 ≤ j.val := by omega
    have hr : (i.val : ℝ) + 1 ≤ j.val := by exact_mod_cast hij
    dsimp only [Cslib.Polygonal.Route.position]
    linarith [hs.2, ht.1]

/-- The actual edge-crossing order agrees with the unique node order on its same refined route. -/
theorem edgeCrossings_refined_nodes_order (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1)) :
    (edgeCrossings width d edge).Pairwise (fun a b =>
      ∀ (ka kb : Fin (((refinedDrawing width hd).route edge).bends + 2)),
        ((refinedDrawing width hd).route edge).point ka = complexPoint (a.location width d) →
        ((refinedDrawing width hd).route edge).point kb = complexPoint (b.location width d) → ka < kb) := by
  have hp := (edgeCrossings_segment_order width d edge).and
    (edgeCrossings_same_segment_order width height hd hfit edge)
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb h ka kb hka hkb => ?_) hp
  obtain ⟨ha, hae⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp ha)
  obtain ⟨hb, hbe⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hb)
  have hea : edge.val = a.edge := (of_decide_eq_true hae).symm
  have heb : edge.val = b.edge := (of_decide_eq_true hbe).symm
  obtain ⟨i, s, hi, hs, hsa⟩ := crossing_prepared_parameter width hd edge hhead ha hea
  obtain ⟨j, t, hj, ht, htb⟩ := crossing_prepared_parameter width hd edge hhead hb heb
  apply (PushPuzzle.Polygonal.Route.mapAtCuts_node_order ((preparedDrawing_isEmbedding width hd).simple edge)
    (preparedDrawing_route_open width hd edge) (toothLevels width d) Complex.reCLM.toLinearMap.toAffineMap
    ka kb i j s t ⟨hs.1.le, hs.2.le⟩ ⟨ht.1.le, ht.2.le⟩ (hka.trans hsa.symm) (hkb.trans htb.symm)).mpr
  exact source_parameters_lt width hd edge hhead ha hea h.1 h.2 i j hi hj hs ht hsa htb

end PushPuzzle.PushS.Comb

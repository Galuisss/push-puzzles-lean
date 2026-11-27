/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPartition
import all PushS.CombPartition
import all PushS.CombPreprocess
import all PushS.CombEvents
import CslibFrontier.Foundations.Data.List.ConsecutivePairs

/-! Geometric uniqueness of the actual indexed segment/tooth encounters. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem site_prepare (width : ℕ) (d : Graph.OrthogonalDrawing) (i : ℕ) :
    (prepare width d).1.getD i (0, 0) = point width (d.1.getD i (0, 0)) := by
  have hz : point width (0, 0) = (0, 0) := by simp [point]
  simpa only [prepare, hz] using List.getD_map (l := d.1) (d := (0, 0)) (n := i) (point width)

/-- Each emitted cut point is strictly inside the horizontal extent of its exact indexed segment. -/
theorem crossing_location_strict (width : ℕ) (d : Graph.OrthogonalDrawing) {c : Crossing}
    (hc : c ∈ crossings width d) :
    ∃ ab, ((prepare width d).2.getD c.edge []).consecutivePairs[c.segment]? = some ab ∧
      min ab.1.1 ab.2.1 < (c.location width d).1 ∧ (c.location width d).1 < max ab.1.1 ab.2.1 := by
  obtain ⟨r, ab, site, hr, hab, hsite, htest, _⟩ := (mem_crossings_iff width d c).mp hc
  have hroute : (prepare width d).2.getD c.edge [] = r := by
    simp only [List.getD_eq_getElem?_getD, hr, Option.getD_some]
  have hv : (prepare width d).1.getD c.vertex (0, 0) = site := by
    simp only [List.getD_eq_getElem?_getD, hsite, Option.getD_some]
  refine ⟨ab, by simpa only [hroute] using hab, ?_⟩
  simp only [Crossing.location, hv]
  rcases htest.1 with h | h <;> omega

/-- Equal actual cut-point positions identify the same original tooth. -/
theorem crossing_location_vertex_eq (width : ℕ) (d : Graph.OrthogonalDrawing)
    (hn : d.1.Nodup) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (he : a.location width d = b.location width d) : a.vertex = b.vertex := by
  have hia := crossing_vertex_lt width d ha
  have hib := crossing_vertex_lt width d hb
  have hma : d.1.getD a.vertex (0, 0) ∈ d.1 := by
    rw [List.getD_eq_getElem _ _ hia]
    exact List.getElem_mem hia
  have hmb : d.1.getD b.vertex (0, 0) ∈ d.1 := by
    rw [List.getD_eq_getElem _ _ hib]
    exact List.getElem_mem hib
  have hx := congrArg Prod.fst he
  simp only [Crossing.location, site_prepare] at hx
  exact (hn.getD_inj hia hib).mp
    (point_column_injective width (hvertices _ hma) (hvertices _ hmb) hx)

private theorem position_mem {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {v : ℕ} (hv : v ∈ G.vertices) :
    Graph.drawingPosition G d v ∈ d.1 := by
  have hi : G.vertices.idxOf v < d.1.length := by
    rw [hd.vertexCount]
    exact List.idxOf_lt_length_of_mem hv
  rw [Graph.drawingPosition, List.getD_eq_getElem _ _ hi]
  exact List.getElem_mem hi

/-- Different actual original routes cannot contribute the same strict tooth encounter. -/
theorem crossing_location_edge_eq (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (he : a.location width d = b.location width d) : a.edge = b.edge := by
  by_contra hne
  have hai : a.edge < G.edges.length := by rw [← hd.edgeCount]; exact crossing_edge_lt width d ha
  have hbi : b.edge < G.edges.length := by rw [← hd.edgeCount]; exact crossing_edge_lt width d hb
  have hpa := crossing_location_supported width hd ha
  have hpb := crossing_location_supported width hd hb
  rw [← he] at hpb
  obtain ⟨v, hv, _, _, hp⟩ := prepare_contacts width hd hai hbi hne hpa hpb
  have hpoint : a.location width d = point width (Graph.drawingPosition G d v) := by
    rw [drawingPosition_prepare] at hp
    exact realPoint_injective hp
  exact crossing_location_ne_point width d hvertices ha _ (hvertices _ (position_mem hd hv)) hpoint

private theorem consecutivePairs_nodup {α : Type} (xs : List α) (hn : xs.Nodup) : xs.consecutivePairs.Nodup := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    cases xs with
    | nil => simp
    | cons b xs =>
      rw [List.consecutivePairs_cons_cons, List.nodup_cons]
      refine ⟨?_, ih hn.tail⟩
      intro hab
      exact (List.nodup_cons.mp hn).1 ((List.of_mem_zip hab).1)

/-- Equal encounters on one original edge identify the same actual segment occurrence. -/
theorem crossing_location_segment_eq (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) {a b : Crossing}
    (ha : a ∈ crossings width d) (hb : b ∈ crossings width d) (hedge : a.edge = b.edge)
    (he : a.location width d = b.location width d) : a.segment = b.segment := by
  obtain ⟨ab, hab, hp⟩ := crossing_location_segment width hd ha
  obtain ⟨cd, hcd, hq⟩ := crossing_location_segment width hd hb
  obtain ⟨ab', hab', hstrict⟩ := crossing_location_strict width d ha
  have habab' : ab = ab' := Option.some.inj (hab.symm.trans hab')
  subst ab'
  rw [← hedge] at hcd
  let route := (prepare width d).2.getD a.edge []
  have hai : a.edge < G.edges.length := by rw [← hd.edgeCount]; exact crossing_edge_lt width d ha
  have hs := prepare_simple width hd a.edge hai
  have hm : ab ∈ route.consecutivePairs := by
    exact List.mem_of_getElem? hab
  have hn : cd ∈ route.consecutivePairs := by
    exact List.mem_of_getElem? hcd
  have heq : ab = cd := by
    by_contra hne
    rw [← he] at hq
    have hc := (hs.2 ab hm cd hn hne _ hp hq).1
    rcases hc with hc | hc
    all_goals have hx := congrArg Prod.fst hc
    all_goals change (((a.location width d).1 : ℤ) : ℝ) = _ at hx
    all_goals have hx' : (a.location width d).1 = _ := Int.cast_inj.mp hx
    all_goals omega
  have hnd := consecutivePairs_nodup route hs.1
  exact (hnd.getElem?_inj (List.getElem?_eq_some_iff.mp hab).1).mp
    (hab.trans ((congrArg some heq).trans hcd.symm))

/-- In a genuine supplied drawing, an actual cut-point position identifies its complete occurrence. -/
theorem crossing_location_injective (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (he : a.location width d = b.location width d) : a = b := by
  have hedge := crossing_location_edge_eq width hd hvertices ha hb he
  exact crossings_key_injective width d ha hb hedge
    (crossing_location_segment_eq width hd ha hb hedge he)
    (crossing_location_vertex_eq width d hd.positionsNodup hvertices ha hb he)

/-- The actual crossing table has distinct physical cut-point locations. -/
theorem crossings_locations_nodup (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width) :
    ((crossings width d).map (Crossing.location width d)).Nodup := by
  apply (crossings_nodup width d).map_on
  intro a ha b hb he
  exact crossing_location_injective width hd hvertices ha hb he

private theorem prepared_height_bounds (width : ℕ) (d : Graph.OrthogonalDrawing)
    (hpoints : ∀ r ∈ d.2, ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ width)
    {edge : ℕ} (hi : edge < d.2.length) {p : Point}
    (hp : p ∈ (prepare width d).2.getD edge []) : 0 ≤ p.2 ∧ p.2 ≤ 2 * width := by
  rw [route_prepare] at hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hr : d.2.getD edge [] ∈ d.2 := by
    rw [List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hbound := hpoints _ hr q hq
  simp only [point]
  omega

/-- Every actual crossing of a supplied strip drawing lies at a nonnegative bounded height. -/
theorem crossing_height_bounds (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d)
    (hpoints : ∀ r ∈ d.2, ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ width)
    {c : Crossing} (hc : c ∈ crossings width d) : 0 ≤ c.height ∧ c.height ≤ 2 * width := by
  obtain ⟨ab, hab, hp⟩ := crossing_location_segment width hd hc
  have hm := List.of_mem_zip (List.mem_of_getElem? hab)
  have ha := prepared_height_bounds width d hpoints (crossing_edge_lt width d hc) hm.1
  have hb := prepared_height_bounds width d hpoints (crossing_edge_lt width d hc)
    (List.mem_of_mem_tail hm.2)
  have hy := (mem_segment_bounds hp).2
  change min (ab.1.2 : ℝ) ab.2.2 ≤ (c.height : ℝ) ∧ (c.height : ℝ) ≤ max (ab.1.2 : ℝ) ab.2.2 at hy
  have hy' : min ab.1.2 ab.2.2 ≤ c.height ∧ c.height ≤ max ab.1.2 ab.2.2 := by exact_mod_cast hy
  omega

private theorem tooth_height_injective (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width)
    {vertex : ℕ} {a b : Crossing} (ha : a ∈ toothCrossings width d vertex)
    (hb : b ∈ toothCrossings width d vertex) (he : a.height = b.height) : a = b := by
  obtain ⟨ha, hav⟩ := tooth_mem width d ha
  obtain ⟨hb, hbv⟩ := tooth_mem width d hb
  apply crossing_location_injective width hd hvertices ha hb
  exact Prod.ext (by simp only [Crossing.location, hav, hbv]) he

/-- The computed tooth list follows strictly increasing actual physical crossing height. -/
theorem toothCrossings_strict (width : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hvertices : ∀ p ∈ d.1, 0 ≤ p.1 ∧ p.1 ≤ width)
    (hpoints : ∀ r ∈ d.2, ∀ p ∈ r, 0 ≤ p.1 ∧ p.1 ≤ width) (vertex : ℕ) :
    (toothCrossings width d vertex).Pairwise (fun a b => a.height < b.height) := by
  have hn := (toothCrossings_perm width d vertex).nodup_iff.mpr ((crossings_nodup width d).filter _)
  have hp := (toothCrossings_pairwise width d vertex).and hn
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) hp
  have hna := (crossing_height_bounds width hd hpoints (tooth_mem width d ha).1).1
  have hnb := (crossing_height_bounds width hd hpoints (tooth_mem width d hb).1).1
  have hne : a.height ≠ b.height := fun he => h.2 (tooth_height_injective width hd hvertices ha hb he)
  have ha' : (a.height.toNat : ℤ) = a.height := Int.toNat_of_nonneg hna
  have hb' : (b.height.toNat : ℤ) = b.height := Int.toNat_of_nonneg hnb
  omega

end PushPuzzle.PushS.Comb

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombRouteOrder
import all PushS.CombPreprocess
import all PushS.CombRouteOrder

/-! The computed tooth ranks agree with the actual strictly ordered prepared columns. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

private theorem prepared_columns_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    ((prepare width d).1.map Prod.fst).Nodup := by
  change ((d.1.map (point width)).map Prod.fst).Nodup
  rw [List.map_map]
  apply hd.positionsNodup.map_on
  intro a ha b hb he
  have hpa := hfit.1 a ha
  have hpb := hfit.1 b hb
  exact point_column_injective width ⟨hpa.1, hpa.2.1⟩ ⟨hpb.1, hpb.2.1⟩ he

private theorem prepared_column_nonneg (width height : ℕ) {d : Graph.OrthogonalDrawing}
    (hfit : Graph.drawingFits d width height) {p : Point} (hp : p ∈ (prepare width d).1) : 0 ≤ p.1 := by
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  have hpa := hfit.1 q hq
  have hs : (0 : ℤ) ≤ stride width := Int.natCast_nonneg _
  have hm := mul_nonneg hs hpa.2.2.1
  simp only [point]
  omega

/-- The actual sorted teeth have distinct physical columns, with every source occurrence retained. -/
theorem vertexOrder_columns_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    ((vertexOrder width d).map (fun sv => sv.1.1)).Nodup := by
  have hp := ((vertexOrder_perm width d).map Prod.fst).map Prod.fst
  have hn := prepared_columns_nodup width height hd hfit
  simp only [List.zipIdx_map_fst] at hp
  simpa only [List.map_map, List.zipIdx_map_fst, Function.comp_def] using hp.nodup_iff.mpr hn

/-- The emitted tooth order follows strictly increasing actual prepared columns. -/
theorem vertexOrder_strict (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    (vertexOrder width d).Pairwise (fun a b => a.1.1 < b.1.1) := by
  have hn : (vertexOrder width d).Pairwise (fun a b => a.1.1 ≠ b.1.1) := by
    simpa only [List.Nodup, List.pairwise_map] using vertexOrder_columns_nodup width height hd hfit
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) ((vertexOrder_pairwise width d).and hn)
  have hma := List.fst_mem_of_mem_zipIdx ((vertexOrder_perm width d).mem_iff.mp ha)
  have hmb := List.fst_mem_of_mem_zipIdx ((vertexOrder_perm width d).mem_iff.mp hb)
  have hpa := prepared_column_nonneg width height hfit hma
  have hpb := prepared_column_nonneg width height hfit hmb
  have ha' : (a.1.1.toNat : ℤ) = a.1.1 := Int.toNat_of_nonneg hpa
  have hb' : (b.1.1.toNat : ℤ) = b.1.1 := Int.toNat_of_nonneg hpb
  omega

private theorem ordered_site (width : ℕ) (d : Graph.OrthogonalDrawing) {v : ℕ} (hv : v < d.1.length) :
    ∃ i : Fin (vertexOrder width d).length,
      i.val = vertexRank width d v ∧ ((vertexOrder width d).get i).2 = v ∧
        ((vertexOrder width d).get i).1 = (prepare width d).1.getD v (0, 0) := by
  have hlen : (vertexOrder width d).length = d.1.length := by
    simpa only [prepare, List.length_map, List.length_zipIdx] using (vertexOrder_perm width d).length_eq
  have hi : vertexRank width d v < (vertexOrder width d).length := by
    rw [hlen]
    exact vertexRank_lt width d hv
  let i : Fin (vertexOrder width d).length := ⟨vertexRank width d v, hi⟩
  have hiv : vertexRank width d v < (List.map Prod.snd (vertexOrder width d)).length := by
    simpa only [List.length_map] using hi
  have hindex : ((vertexOrder width d).map Prod.snd).idxOf v <
      ((vertexOrder width d).map Prod.snd).length := by
    change vertexRank width d v < _
    exact hiv
  have hid : (List.map Prod.snd (vertexOrder width d))[vertexRank width d v]'hiv = v := by
    exact List.getElem_idxOf hindex
  have hsecond : ((vertexOrder width d).get i).2 = v := by
    simpa only [List.getElem_map, List.get_eq_getElem, i] using hid
  have hm := List.mem_zipIdx_iff_getElem?.mp
    ((vertexOrder_perm width d).mem_iff.mp (List.get_mem (vertexOrder width d) i))
  rw [hsecond] at hm
  refine ⟨i, rfl, hsecond, ?_⟩
  simp only [List.getD_eq_getElem?_getD, hm, Option.getD_some]

/-- The computed source tooth ranks agree exactly with the geometric prepared-column order. -/
theorem vertexRank_column_lt_iff (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    {a b : ℕ} (ha : a < d.1.length) (hb : b < d.1.length) :
    vertexRank width d a < vertexRank width d b ↔
      ((prepare width d).1.getD a (0, 0)).1 < ((prepare width d).1.getD b (0, 0)).1 := by
  obtain ⟨i, hi, _, hia⟩ := ordered_site width d ha
  obtain ⟨j, hj, _, hjb⟩ := ordered_site width d hb
  have hm := List.pairwise_iff_get.mp (vertexOrder_strict width height hd hfit)
  constructor
  · intro h
    simpa only [hia, hjb] using hm i j (by change i.val < j.val; omega)
  · intro h
    by_contra hnot
    have hge : j.val ≤ i.val := by omega
    rcases lt_or_eq_of_le hge with hlt | heq
    · have hs := hm j i hlt
      rw [hia, hjb] at hs
      omega
    · have he : i = j := Fin.ext heq.symm
      have hs := congrArg (fun k : Fin (vertexOrder width d).length => ((vertexOrder width d).get k).1.1) he
      rw [hia, hjb] at hs
      omega

/-- On each original segment, successive emitted encounters follow its actual traversal direction. -/
theorem edgeCrossings_same_segment_order (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : ℕ) :
    (edgeCrossings width d edge).Pairwise (fun a b => a.segment = b.segment →
      if a.forward then (a.location width d).1 < (b.location width d).1
      else (b.location width d).1 < (a.location width d).1) := by
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb hk hs => ?_) (edgeCrossings_strict width d edge)
  obtain ⟨ha', hae⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp ha)
  obtain ⟨hb', hbe⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hb)
  have hf := crossing_forward_eq width d ha' hb' ((of_decide_eq_true hae).trans (of_decide_eq_true hbe).symm) hs
  have hva := crossing_vertex_lt width d ha'
  have hvb := crossing_vertex_lt width d hb'
  have hra := vertexRank_lt width d hva
  have hrb := vertexRank_lt width d hvb
  simp only [routeKey, hs, ← hf] at hk
  cases hdir : a.forward with
  | false =>
    simp only [hdir, Bool.false_eq_true, ite_false] at hk ⊢
    exact (vertexRank_column_lt_iff width height hd hfit hvb hva).mp (by omega)
  | true =>
    simp only [hdir, ite_true] at hk ⊢
    exact (vertexRank_column_lt_iff width height hd hfit hva hvb).mp (by omega)

end PushPuzzle.PushS.Comb

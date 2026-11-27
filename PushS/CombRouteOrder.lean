/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCrossingGeometry
import all PushS.CombPartition
import all PushS.CombOrdering

/-! The actual edge-crossing keys identify occurrences and preserve strict source-segment order. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private theorem vertexRank_injective (width : ℕ) (d : Graph.OrthogonalDrawing)
    {a b : ℕ} (ha : a < d.1.length) (he : vertexRank width d a = vertexRank width d b) : a = b := by
  have hlen : (vertexOrder width d).length = d.1.length := by
    simpa only [prepare, List.length_map, List.length_zipIdx] using (vertexOrder_perm width d).length_eq
  have hi := vertexRank_lt width d ha
  change ((vertexOrder width d).map Prod.snd).idxOf a < d.1.length at hi
  have hm : a ∈ (vertexOrder width d).map Prod.snd := List.idxOf_lt_length_iff.mp (by
    simpa only [List.length_map, hlen] using hi)
  exact (List.idxOf_inj hm).mp he

private theorem crossing_forward_eq (width : ℕ) (d : Graph.OrthogonalDrawing)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (he : a.edge = b.edge) (hs : a.segment = b.segment) : a.forward = b.forward := by
  obtain ⟨r, ab, _, hr, hab, _, _, _, hf⟩ := (mem_crossings_iff width d a).mp ha
  obtain ⟨r', ab', _, hr', hab', _, _, _, hf'⟩ := (mem_crossings_iff width d b).mp hb
  rw [← he] at hr'
  have hrr : r = r' := Option.some.inj (hr.symm.trans hr')
  subst r'
  rw [← hs] at hab'
  have hseg : ab = ab' := Option.some.inj (hab.symm.trans hab')
  subst ab'
  exact hf.trans hf'.symm

private theorem routeKey_div (width : ℕ) (d : Graph.OrthogonalDrawing) {c : Crossing}
    (hc : c ∈ crossings width d) : routeKey width d c / (d.1.length + 1) = c.segment := by
  have hv := vertexRank_lt width d (crossing_vertex_lt width d hc)
  have hr : (if c.forward then vertexRank width d c.vertex else d.1.length - vertexRank width d c.vertex) <
      d.1.length + 1 := by split <;> omega
  rw [routeKey, Nat.mul_comm c.segment, Nat.mul_add_div (by omega : 0 < d.1.length + 1),
    Nat.div_eq_of_lt hr, Nat.add_zero]

/-- On one actual original edge, its segment/direction key determines the complete crossing occurrence. -/
theorem routeKey_injective (width : ℕ) (d : Graph.OrthogonalDrawing)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (hedge : a.edge = b.edge) (hkey : routeKey width d a = routeKey width d b) : a = b := by
  have hs : a.segment = b.segment := by
    have h := congrArg (fun key => key / (d.1.length + 1)) hkey
    simpa only [routeKey_div width d ha, routeKey_div width d hb] using h
  have hf := crossing_forward_eq width d ha hb hedge hs
  have hva := vertexRank_lt width d (crossing_vertex_lt width d ha)
  have hvb := vertexRank_lt width d (crossing_vertex_lt width d hb)
  have hv : vertexRank width d a.vertex = vertexRank width d b.vertex := by
    simp only [routeKey, hs, hf] at hkey
    cases hb' : b.forward <;> simp only [hb', Bool.false_eq_true, ite_false, ite_true] at hkey <;> omega
  exact crossings_key_injective width d ha hb hedge hs
    (vertexRank_injective width d (crossing_vertex_lt width d ha) hv)

private theorem edge_key_pairwise (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeCrossings width d edge).Pairwise (fun a b => routeKey width d a ≤ routeKey width d b) := by
  let decorated := ((crossings width d).filter fun c => decide (c.edge = edge)).map fun c =>
    (routeKey width d c, c)
  let sorted := Sort.run Prod.fst (0, ⟨0, 0, 0, 0, false⟩) decorated
  have hk (p : ℕ × Crossing) (hp : p ∈ sorted) : p.1 = routeKey width d p.2 := by
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp ((Sort.run_perm Prod.fst (0, ⟨0, 0, 0, 0, false⟩) decorated).mem_iff.mp hp)
    rfl
  have hp := Sort.run_pairwise Prod.fst (0, ⟨0, 0, 0, 0, false⟩) decorated
  have ho : sorted.Pairwise (fun a b => routeKey width d a.2 ≤ routeKey width d b.2) := by
    exact List.Pairwise.imp_of_mem (fun {a b} ha hb h => by simpa only [hk a ha, hk b hb] using h) hp
  simpa only [edgeCrossings, List.pairwise_map] using ho

/-- Each emitted edge list follows strictly increasing actual source segment/direction keys. -/
theorem edgeCrossings_strict (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeCrossings width d edge).Pairwise (fun a b => routeKey width d a < routeKey width d b) := by
  have hn := (edgeCrossings_perm width d edge).nodup_iff.mpr ((crossings_nodup width d).filter _)
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) ((edge_key_pairwise width d edge).and hn)
  obtain ⟨ha, hae⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp ha)
  obtain ⟨hb, hbe⟩ := List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hb)
  have hne : routeKey width d a ≠ routeKey width d b := fun he => h.2
    (routeKey_injective width d ha hb ((of_decide_eq_true hae).trans (of_decide_eq_true hbe).symm) he)
  omega

/-- The emitted crossings of one original edge never move backwards in its source segment array. -/
theorem edgeCrossings_segment_order (width : ℕ) (d : Graph.OrthogonalDrawing) (edge : ℕ) :
    (edgeCrossings width d edge).Pairwise (fun a b => a.segment ≤ b.segment) := by
  refine List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) (edge_key_pairwise width d edge)
  have ha' := (List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp ha)).1
  have hb' := (List.mem_filter.mp ((edgeCrossings_perm width d edge).mem_iff.mp hb)).1
  have hd := Nat.div_le_div_right h (c := d.1.length + 1)
  simpa only [routeKey_div width d ha', routeKey_div width d hb'] using hd

end PushPuzzle.PushS.Comb

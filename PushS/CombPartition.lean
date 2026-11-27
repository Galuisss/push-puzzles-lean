/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombCore
import all PushS.CombTopology
import Mathlib.Data.Multiset.Bind
import Mathlib.Data.List.Sigma
import CslibFrontier.Foundations.Data.List.Lookup

/-! The actual contour uses each original incidence and each marked crossing exactly once. -/

public section

namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

private def incidenceMap {E : Type} (edge : E → ℕ) :
    Multiset (NCL.WeightedPort E) →+ Multiset Token where
  toFun := Multiset.map (fun p => Token.tip (edge p.1.edge) p.1.dir)
  map_zero' := Multiset.map_zero _
  map_add' := Multiset.map_add _

private theorem coe_flatten_ofFn {α : Type} (n : ℕ) (f : Fin n → List α) :
    (↑(List.ofFn f).flatten : Multiset α) = ∑ i, (↑(f i) : Multiset α) := by
  induction n with
  | zero => simp
  | succ n ih => simp only [List.ofFn_succ, List.flatten_cons, Fin.sum_univ_succ, ← Multiset.coe_add, ih]

/-- The original native weighted graph lists exactly one tip of each direction of every edge. -/
theorem native_tips_perm (g : NCL.AndOrGraph) (hg : NCL.SourceValid g) :
    ((g.vertices.flatMap NCL.Vertex.ports).map fun p => incidenceToken p.1).Perm
      ((List.ofFn fun e : Fin g.edgeCount => [.tip e.val false, .tip e.val true]).flatten) := by
  obtain ⟨weight, hw⟩ := hg.wellFormed
  have hm := congrArg (incidenceMap Fin.val) hw
  have hraw := congrArg (incidenceMap id) (g.graph_portMultiset hg.1)
  simp only [incidenceMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    NCL.WeightedPort.map, NCL.Port.map, Multiset.map_map, Function.comp_def] at hraw
  simp only [map_sum, incidenceMap, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Multiset.map_add, Multiset.map_singleton] at hm
  have heq : (↑((g.vertices.flatMap NCL.Vertex.ports).map fun p => incidenceToken p.1) : Multiset Token) =
      ∑ e : Fin g.edgeCount, ({Token.tip e.val false} + {Token.tip e.val true}) := by
    simpa only [Multiset.map_coe, incidenceToken, id_eq] using hraw.symm.trans hm
  apply Multiset.coe_eq_coe.mp
  rw [heq]
  rw [coe_flatten_ofFn]
  rfl

private theorem edge_tips_nodup (n : ℕ) :
    ((List.ofFn fun e : Fin n => [Token.tip e.val false, Token.tip e.val true]).flatten).Nodup := by
  rw [List.nodup_flatten]
  constructor
  · intro xs hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    simp
  · rw [List.pairwise_ofFn]
    intro i j hij
    apply List.disjoint_left.mpr
    intro token hi hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
    rcases hi with rfl | rfl <;>
      simp only [Token.tip.injEq, Bool.false_eq_true, Bool.true_eq_false, and_false, false_or,
        and_true, or_false] at hj <;>
      omega

/-- No original native incidence is repeated in the complete source vertex list. -/
theorem native_tips_nodup (g : NCL.AndOrGraph) (hg : NCL.SourceValid g) :
    ((g.vertices.flatMap NCL.Vertex.ports).map fun p => incidenceToken p.1).Nodup :=
  (native_tips_perm g hg).nodup_iff.mpr (edge_tips_nodup g.edgeCount)

private theorem coreTemplate_tip_mem (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    (hlen : ports.length = 3) {edge : ℕ} {dir : Bool} :
    Token.tip edge dir ∈ (coreTemplate vertex ports).order ↔
      Token.tip edge dir ∈ ports.map (fun p => incidenceToken p.1) := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  unfold coreTemplate
  extract_lets pa pb pc kind ta tb tc inside outside
  split_ifs <;> simp [ta, tb, tc, inside, outside, pa, pb, pc]

private theorem coreTemplate_no_mark (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    (edge slot v : ℕ) (side : Bool) :
    Token.mark edge slot v side ∉ (coreTemplate vertex ports).order := by
  unfold coreTemplate
  extract_lets a b c kind ta tb tc inside outside
  split_ifs <;> simp [ta, tb, tc, inside, outside, incidenceToken]

private theorem coreTemplate_rotation_owner (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    {v : ℕ} {inside : Bool}
    (h : Token.rotation v inside ∈ (coreTemplate vertex ports).order) : v = vertex := by
  unfold coreTemplate at h
  extract_lets a b c kind ta tb tc inner outer at h
  split_ifs at h <;> simp [ta, tb, tc, inner, outer, incidenceToken] at h
  all_goals omega

private theorem coreTemplate_order_nodup (vertex : ℕ) (ports : List (NCL.WeightedPort ℕ))
    (hlen : ports.length = 3) (hp : (ports.map fun p => incidenceToken p.1).Nodup) :
    (coreTemplate vertex ports).order.Nodup := by
  obtain ⟨a, b, c, rfl⟩ := List.length_eq_three.mp hlen
  simp only [List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
    List.not_mem_nil, or_false, not_or, List.nodup_nil, and_true] at hp
  unfold coreTemplate
  extract_lets pa pb pc kind ta tb tc inside outside
  split_ifs <;>
    simp [ta, tb, tc, inside, outside, pa, pb, pc, incidenceToken] at hp ⊢ <;>
    tauto

/-- Every actual crossing retains an in-bounds original vertex position. -/
theorem crossing_vertex_lt (width : ℕ) (d : Graph.OrthogonalDrawing) {c : Crossing}
    (hc : c ∈ crossings width d) : c.vertex < d.1.length := by
  obtain ⟨_, _, site, _, _, hv, _⟩ := (mem_crossings_iff width d c).mp hc
  have hz : (site, c.vertex) ∈ (prepare width d).1.zipIdx := List.mem_zipIdx_iff_getElem?.mpr hv
  have hi := List.snd_lt_of_mem_zipIdx hz
  simpa only [prepare, List.length_map, Nat.add_zero] using hi

private theorem tooth_mem (width : ℕ) (d : Graph.OrthogonalDrawing) {v : ℕ} {c : Crossing}
    (hc : c ∈ toothCrossings width d v) : c ∈ crossings width d ∧ c.vertex = v := by
  simpa only [List.mem_filter, decide_eq_true_eq] using
    (toothCrossings_perm width d v).mem_iff.mp hc

private theorem crossing_token_injective (width : ℕ) (d : Graph.OrthogonalDrawing) (side : Bool)
    {a b : Crossing} (ha : a ∈ crossings width d) (hb : b ∈ crossings width d)
    (h : a.token side = b.token side) : a = b := by
  have hh := Token.mark.inj h
  exact crossings_key_injective width d ha hb hh.1 hh.2.1 hh.2.2.1

private theorem tooth_side_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) (v : ℕ) (side : Bool) :
    ((toothCrossings width d v).map fun c => c.token side).Nodup := by
  have hn := (toothCrossings_perm width d v).nodup_iff.mpr ((crossings_nodup width d).filter _)
  apply hn.map_on
  intro a ha b hb h
  exact crossing_token_injective width d side (tooth_mem width d ha).1 (tooth_mem width d hb).1 h

private theorem fan_tips_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {v : ℕ} (hv : v < input.graph.vertices.length) :
    ((fan width input v).map fun p => incidenceToken p.1).Nodup := by
  have hn := native_tips_nodup input.graph hg
  rw [List.map_flatMap] at hn
  have hv' : input.graph.vertices.getD v ⟨[], 0⟩ ∈ input.graph.vertices :=
    by
      rw [List.getD_eq_get _ _ ⟨v, hv⟩]
      exact List.get_mem _ _
  exact ((fan_perm width input v).map (fun p => incidenceToken p.1)).nodup_iff.mpr
    ((List.nodup_flatMap.mp hn).1 _ hv')

/-- The actual token block of each original valid vertex contains no repeated port. -/
theorem vertexBlock_order_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {v : ℕ} (hv : v < input.graph.vertices.length) : (vertexBlock width input v).order.Nodup := by
  let hits := toothCrossings width input.drawing v
  let b := coreTemplate v (fan width input v)
  have hl := tooth_side_nodup width input.drawing v false
  have hr : (hits.reverse.map fun c => c.token true).Nodup := by
    rw [List.map_reverse, List.nodup_reverse]
    exact tooth_side_nodup width input.drawing v true
  have hc := coreTemplate_order_nodup v (fan width input v) (fan_length width input hg hv)
    (fan_tips_nodup width input hg hv)
  have hlc : List.Disjoint (hits.map fun c => c.token false) b.order := by
    apply List.disjoint_left.mpr
    intro token hleft hcore
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hleft
    exact coreTemplate_no_mark v (fan width input v) c.edge c.segment c.vertex false hcore
  have hcr : List.Disjoint b.order (hits.reverse.map fun c => c.token true) := by
    apply List.disjoint_left.mpr
    intro token hcore hright
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hright
    exact coreTemplate_no_mark v (fan width input v) c.edge c.segment c.vertex true hcore
  have hlr : List.Disjoint (hits.map fun c => c.token false) (hits.reverse.map fun c => c.token true) := by
    apply List.disjoint_left.mpr
    intro token hleft hright
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hleft
    obtain ⟨b, _, h⟩ := List.mem_map.mp hright
    exact Bool.noConfusion (Token.mark.inj h).2.2.2
  exact (hl.append hc hlc).append hr (List.disjoint_append_left.mpr ⟨hlr, hcr⟩)

private theorem vertexBlock_tip_mem (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    {v : ℕ} (hv : v < input.graph.vertices.length) {edge : ℕ} {dir : Bool} :
    Token.tip edge dir ∈ (vertexBlock width input v).order ↔
      Token.tip edge dir ∈ (input.graph.vertices.getD v ⟨[], 0⟩).ports.map (fun p => incidenceToken p.1) := by
  simp only [vertexBlock, List.mem_append, List.mem_map, Crossing.token, reduceCtorEq,
    and_false, exists_false, false_or, or_false]
  apply (coreTemplate_tip_mem v (fan width input v) (fan_length width input hg hv)).trans
  simpa only [List.mem_map] using
    ((fan_perm width input v).map (fun p => incidenceToken p.1)).mem_iff
      (a := Token.tip edge dir)

private theorem vertexBlock_mark_owner (width : ℕ) (input : Input) {v edge slot tooth : ℕ} {side : Bool}
    (h : Token.mark edge slot tooth side ∈ (vertexBlock width input v).order) : tooth = v := by
  simp only [vertexBlock, List.mem_append] at h
  rcases h with (h | h) | h
  · obtain ⟨c, hc, heq⟩ := List.mem_map.mp h
    exact (Token.mark.inj heq).2.2.1.symm.trans (tooth_mem width input.drawing hc).2
  · exact False.elim (coreTemplate_no_mark v (fan width input v) edge slot tooth side h)
  · obtain ⟨c, hc, heq⟩ := List.mem_map.mp h
    exact (Token.mark.inj heq).2.2.1.symm.trans
      (tooth_mem width input.drawing (List.mem_reverse.mp hc)).2

private theorem vertexBlock_rotation_owner (width : ℕ) (input : Input) {v vertex : ℕ} {side : Bool}
    (h : Token.rotation vertex side ∈ (vertexBlock width input v).order) : vertex = v := by
  simp only [vertexBlock, List.mem_append, List.mem_map, Crossing.token, reduceCtorEq,
    and_false, exists_false, false_or, or_false] at h
  exact coreTemplate_rotation_owner v (fan width input v) h

private theorem ordered_native_tips_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) :
    ((vertexOrder width input.drawing).flatMap fun sv =>
      (input.graph.vertices.getD sv.2 ⟨[], 0⟩).ports.map fun p => incidenceToken p.1).Nodup := by
  have hp := (vertexOrder_perm width input.drawing).flatMap_right
    (fun sv => (input.graph.vertices.getD sv.2 ⟨[], 0⟩).ports.map fun p => incidenceToken p.1)
  apply hp.nodup_iff.mpr
  have hlen : input.graph.vertices.length = (prepare width input.drawing).1.length := by
    simpa only [prepare, List.length_map] using hcount.symm
  have hlookup := List.map_getD_zipIdx (prepare width input.drawing).1 input.graph.vertices ⟨[], 0⟩ hlen
  have hex := congrArg (fun vs : List (NCL.Vertex ℕ) =>
    vs.flatMap fun v => v.ports.map fun p => incidenceToken p.1) hlookup
  simp only [List.flatMap_map] at hex
  rw [hex, ← List.map_flatMap]
  exact native_tips_nodup input.graph hg

/-- The complete computed contour has distinct actual ports, derived from the source graph. -/
theorem cut_order_nodup (width : ℕ) (input : Input) (hg : NCL.SourceValid input.graph)
    (hcount : input.drawing.1.length = input.graph.vertices.length) : (cut width input).order.Nodup := by
  have htips := (List.nodup_flatMap.mp (ordered_native_tips_nodup width input hg hcount)).2
  have hind : (vertexOrder width input.drawing).Pairwise (fun a b => a.2 ≠ b.2) := by
    have hn := (vertexOrder_perm width input.drawing).map Prod.snd
    simpa only [List.Nodup, List.pairwise_map] using hn.nodup_iff.mpr
      (List.nodup_zipIdx_map_snd (prepare width input.drawing).1)
  simp only [cut, List.flatMap_map]
  apply List.nodup_flatMap.mpr
  constructor
  · intro sv hsv
    apply vertexBlock_order_nodup width input hg
    have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hsv)
    simp only [prepare, List.length_map, Nat.add_zero] at hi
    omega
  · apply List.Pairwise.imp_of_mem (fun {a b} ha hb h => ?_) (htips.and hind)
    have hav : a.2 < input.graph.vertices.length := by
      have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp ha)
      simp only [prepare, List.length_map, Nat.add_zero] at hi
      omega
    have hbv : b.2 < input.graph.vertices.length := by
      have hi := List.snd_lt_of_mem_zipIdx ((vertexOrder_perm width input.drawing).mem_iff.mp hb)
      simp only [prepare, List.length_map, Nat.add_zero] at hi
      omega
    apply List.disjoint_left.mpr
    intro token hta htb
    cases token with
    | tip edge dir =>
      exact List.disjoint_left.mp h.1
        ((vertexBlock_tip_mem width input hg hav).mp hta)
        ((vertexBlock_tip_mem width input hg hbv).mp htb)
    | mark edge slot vertex side =>
      exact h.2 ((vertexBlock_mark_owner width input hta).symm.trans
        (vertexBlock_mark_owner width input htb))
    | rotation vertex side =>
      exact h.2 ((vertexBlock_rotation_owner width input hta).symm.trans
        (vertexBlock_rotation_owner width input htb))

end PushPuzzle.PushS.Comb

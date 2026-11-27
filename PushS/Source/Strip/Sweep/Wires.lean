/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Vertices

/-!
# Ordinary wire cells of the actual strip sweep

Away from source centers and the explicitly enumerated crossing sites, one original carrier
passes through each visited grid site. Its actual unit path supplies exactly two incident arcs.
The preceding/following split therefore has the cup, straight, or cap arity.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.wire_slice`: two actual local ports, on one original carrier.
* `PushPuzzle.NCL.Strip.Sweep.wire_arities`: the three wire-cell arities.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

private theorem filter_pairs_nil {r : Route} {p : Point} (hp : p ∉ r) :
    r.consecutivePairs.filter (fun q => decide (q.1 = p ∨ q.2 = p)) = [] := by
  apply List.filter_eq_nil_iff.mpr
  intro q hq
  simp only [decide_eq_true_eq, not_or]
  have hm := List.of_mem_zip hq
  exact ⟨fun h => hp (h ▸ hm.1), fun h => hp (h ▸ List.mem_of_mem_tail hm.2)⟩

private theorem interior_pairs_length {r : Route} (hn : r.Nodup) {p : Point}
    (hp : p ∈ r) (hh : r.head? ≠ some p) (ht : r.getLast? ≠ some p) :
    (r.consecutivePairs.filter (fun q => decide (q.1 = p ∨ q.2 = p))).length = 2 := by
  obtain ⟨s, t, rfl⟩ := List.mem_iff_append.mp hp
  have hs : s ≠ [] := by intro h; subst s; exact hh rfl
  have htn : t ≠ [] := by
    intro h
    subst t
    apply ht
    simp
  have hnd := List.nodup_append.mp hn
  have hsn : p ∉ s := fun hp => hnd.2.2 p hp p (by simp) rfl
  have htnp : p ∉ t := (List.nodup_cons.mp hnd.2.1).1
  obtain ⟨b, t, rfl⟩ := List.exists_cons_of_ne_nil htn
  rw [List.consecutivePairs_append hs (by simp), List.filter_append,
    List.consecutivePairs_cons_cons, filter_pairs_nil hsn]
  simp only [List.filter_cons, List.head_cons, true_or, or_true, decide_true, ite_true,
    filter_pairs_nil htnp, List.nil_append, List.length_cons, List.length_nil]

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

private theorem touch_iff (a : Arc R) (p : Point) :
    (a.pair R).1 = p ∨ (a.pair R).2 = p ↔ a.lower R = p ∨ a.upper R = p := by
  rcases a.pair_eq R with h | h
  · simp only [h]
  · simp only [h, or_comm]

private def carrierIncidences (e : E) (p : Point) : List (Arc R) :=
  (arcs R [e]).filter (fun a => decide ((a.pair R).1 = p ∨ (a.pair R).2 = p))

private theorem mem_carrierIncidences (e : E) (p : Point) (a : Arc R) :
    a ∈ carrierIncidences R e p ↔ a.edge = e ∧ (a.lower R = p ∨ a.upper R = p) := by
  simp only [carrierIncidences, List.mem_filter, mem_arcs, List.mem_singleton,
    decide_eq_true_eq, touch_iff]

private theorem carrierIncidences_length (e : E) {p : Point} (hp : p ∈ R.unitRoute e)
    (hc : ∀ v, p ≠ R.center v) : (carrierIncidences R e p).length = 2 := by
  have hm : (arcs R [e]).map (PushPuzzle.NCL.Strip.Sweep.Arc.pair R) = (R.unitRoute e).consecutivePairs := by
    simp only [arcs, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.map_ofFn]
    exact List.ofFn_get _
  have hmap : (carrierIncidences R e p).map (PushPuzzle.NCL.Strip.Sweep.Arc.pair R) =
      (R.unitRoute e).consecutivePairs.filter (fun q => decide (q.1 = p ∨ q.2 = p)) := by
    rw [← hm, List.filter_map]
    rfl
  have hh : (R.unitRoute e).head? ≠ some p := by
    intro h
    rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_head] at h
    exact hc (R.endpoint e false) (Option.some.inj h).symm
  have ht : (R.unitRoute e).getLast? ≠ some p := by
    intro h
    rw [PushPuzzle.NCL.Strip.Environment.unitRoute, subdivide_last (R.route_orthogonal e)] at h
    exact hc (R.endpoint e true) (Option.some.inj h).symm
  have hl := interior_pairs_length (R.unitRoute_nodup e) hp hh ht
  rw [← hmap, List.length_map] at hl
  exact hl

/-- Away from centers and actual crossing events, a visited site has one original carrier. -/
theorem carrier_unique_at {es : List E} {p : Point} {e f : E} (he : e ∈ es) (hf : f ∈ es)
    (hp : p ∈ R.unitRoute e) (hq : p ∈ R.unitRoute f)
    (hc : ∀ v, p ≠ R.center v) (hx : ∀ c ∈ R.events es, p ≠ c.site R) : f = e := by
  by_contra hne
  obtain ⟨c, hm, hsite, _⟩ := R.nonvertex_contact_event es hf he hne
    ((R.mem_unitRoute f p).mp hq) ((R.mem_unitRoute e p).mp hp)
    (fun v h => hc v (realPoint_injective h))
  exact hx c hm (realPoint_injective hsite)

/-- Each ordinary visited site has two local arcs, both belonging to the same original edge. -/
theorem wire_slice {es : List E} (hes : es.Nodup) {p : Point}
    (hp : ∃ e ∈ es, p ∈ R.unitRoute e)
    (hc : ∀ v, p ≠ R.center v) (hx : ∀ c ∈ R.events es, p ≠ c.site R) :
    ∃ e ∈ es,
      ((slice R es p).incoming ++ (slice R es p).outgoing).length = 2 ∧
        ∀ a ∈ (slice R es p).incoming ++ (slice R es p).outgoing, a.edge = e := by
  obtain ⟨e, he, hp⟩ := hp
  have unique {a : Arc R} (ha : a ∈ (slice R es p).incoming ++ (slice R es p).outgoing) :
      a.edge = e := by
    have hlocal : a.edge ∈ es ∧ (a.lower R = p ∨ a.upper R = p) := by
      rcases List.mem_append.mp ha with ha | ha
      · have h := (mem_slice_incoming R es p a).mp ha
        exact ⟨h.1, Or.inr h.2⟩
      · have h := (mem_slice_outgoing R es p a).mp ha
        exact ⟨h.1, Or.inl h.2⟩
    have hat := (touch_iff R a p).mpr hlocal.2
    have ham : p ∈ R.unitRoute a.edge := by
      apply (R.mem_unitRoute a.edge p).mpr
      rcases hat with h | h
      · exact h ▸ (a.endpoints_mem R).1
      · exact h ▸ (a.endpoints_mem R).2
    exact carrier_unique_at R he hlocal.1 hp ham hc hx
  have hmem (a : Arc R) :
      a ∈ (slice R es p).incoming ++ (slice R es p).outgoing ↔
        a ∈ carrierIncidences R e p := by
    constructor
    · intro ha
      apply (mem_carrierIncidences R e p a).mpr
      refine ⟨unique ha, ?_⟩
      rcases List.mem_append.mp ha with ha | ha
      · exact Or.inr ((mem_slice_incoming R es p a).mp ha).2
      · exact Or.inl ((mem_slice_outgoing R es p a).mp ha).2
    · intro ha
      obtain ⟨hae, ha⟩ := (mem_carrierIncidences R e p a).mp ha
      rcases ha with ha | ha
      · exact List.mem_append_right _ ((mem_slice_outgoing R es p a).mpr ⟨hae ▸ he, ha⟩)
      · exact List.mem_append_left _ ((mem_slice_incoming R es p a).mpr ⟨hae ▸ he, ha⟩)
  have hn : ((slice R es p).incoming ++ (slice R es p).outgoing).Nodup := by
    rw [List.nodup_append]
    refine ⟨(frontier_nodup R hes _).filter _, (frontier_nodup R hes _).filter _, ?_⟩
    intro a ha b hb hab
    subst b
    have hu := ((mem_slice_incoming R es p a).mp ha).2
    have hl := ((mem_slice_outgoing R es p a).mp hb).2
    have hlt := a.level_lt R
    rw [hu, hl] at hlt
    exact (lt_self_iff_false _).mp hlt
  have hn' : (carrierIncidences R e p).Nodup :=
    (arcs_nodup R (List.nodup_singleton e)).filter _
  have hperm := (List.perm_ext_iff_of_nodup hn hn').mpr hmem
  exact ⟨e, he, hperm.length_eq.trans (carrierIncidences_length R e hp hc), fun _ ha => unique ha⟩

/-- The actual ordinary wire slice is a cup, a straight wire, or a cap. -/
theorem wire_arities {es : List E} (hes : es.Nodup) {p : Point}
    (hp : ∃ e ∈ es, p ∈ R.unitRoute e)
    (hc : ∀ v, p ≠ R.center v) (hx : ∀ c ∈ R.events es, p ≠ c.site R) :
    ((slice R es p).incoming.length = 0 ∧ (slice R es p).outgoing.length = 2) ∨
      ((slice R es p).incoming.length = 1 ∧ (slice R es p).outgoing.length = 1) ∨
        ((slice R es p).incoming.length = 2 ∧ (slice R es p).outgoing.length = 0) := by
  obtain ⟨_, _, hl, _⟩ := wire_slice R hes hp hc hx
  rw [List.length_append] at hl
  omega

end PushPuzzle.NCL.Strip.Sweep

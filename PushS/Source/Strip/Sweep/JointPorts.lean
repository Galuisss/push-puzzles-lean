/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Joints

/-!
# Actual local incidences of the unit subdivision

The two adjacent traversal segments are exactly the unit arcs on the same original carrier
meeting an interior joint. Reading incoming ports before outgoing ports changes only their order.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.localPorts`: actual incoming and outgoing weighted ports at a grid site.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.joint_arc_iff`: actual joint incidences identify the two adjacent segments.
* `PushPuzzle.NCL.Strip.Sweep.joint_ports_perm`: the actual slice recovers an actual joint's weighted ports.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal ConstraintGraph

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

namespace Arc

open Cslib.Complexity Cslib.Complexity.NCL

/-- Either endpoint of an actual unit arc is on its original unit traversal. -/
theorem endpoint_mem_unitRoute (a : Arc R) (d : Bool) :
    a.endpoint R d ∈ R.unitRoute a.edge := by
  apply (R.mem_unitRoute _ _).mpr
  cases d
  · exact (a.canonical_endpoints_mem R).1
  · exact (a.canonical_endpoints_mem R).2

end Arc

/-- Each original endpoint center belongs to that edge's actual unit traversal. -/
theorem center_endpoint_mem_unitRoute (e : E) (d : Bool) :
    R.center (R.endpoint e d) ∈ R.unitRoute e := by
  have hp := portArc_endpoint R e d
  have hm : R.center (R.endpoint e d) ∈ R.unitRoute (portArc R e d).edge :=
    hp ▸ (portArc R e d).endpoint_mem_unitRoute R ((portArc R e d).reversed R ^^ d)
  simpa only [(portArc_spec R e d).1] using hm

/-- Every actual interior joint is a grid site on its own original carrier. -/
theorem unitPoint_joint_mem (j : Subdivision.Joint (jointCount R)) :
    unitPoint R (.inr j) ∈ R.unitRoute j.1 := by
  rw [unitPoint_joint_get]
  exact List.getElem_mem _

/-- The unit arcs on a joint's original carrier that meet it are its two adjacent segments. -/
theorem joint_arc_iff (j : Subdivision.Joint (jointCount R)) (a : Arc R) :
    a.edge = j.1 ∧ (a.lower R = unitPoint R (.inr j) ∨ a.upper R = unitPoint R (.inr j)) ↔
      a = segmentEquiv R ⟨j.1, j.2.castSucc⟩ ∨ a = segmentEquiv R ⟨j.1, j.2.succ⟩ := by
  rcases j with ⟨e, j⟩
  constructor
  · rintro ⟨he, hp⟩
    rcases a with ⟨f, i⟩
    dsimp only at he
    subst f
    have ht : ((PushPuzzle.NCL.Strip.Sweep.Arc.pair R ⟨e, i⟩).1 = unitPoint R (.inr ⟨e, j⟩)) ∨
        ((PushPuzzle.NCL.Strip.Sweep.Arc.pair R ⟨e, i⟩).2 = unitPoint R (.inr ⟨e, j⟩)) := by
      rcases (PushPuzzle.NCL.Strip.Sweep.Arc.pair_eq R ⟨e, i⟩) with h | h
      · simpa only [h] using hp
      · simpa only [h, or_comm] using hp
    simp only [PushPuzzle.NCL.Strip.Sweep.Arc.pair_at_index, unitPoint_joint_get] at ht
    rcases ht with h | h
    · right
      have hi := (R.unitRoute_nodup e).getElem_inj_iff.mp h
      exact congrArg (fun k => PushPuzzle.NCL.Strip.Sweep.Arc.mk e k) (Fin.ext hi)
    · left
      have hi := (R.unitRoute_nodup e).getElem_inj_iff.mp h
      apply congrArg (fun k => PushPuzzle.NCL.Strip.Sweep.Arc.mk e k)
      apply Fin.ext
      change i.val = j.val
      omega
  · rintro (rfl | rfl)
    · refine ⟨rfl, ?_⟩
      have h := joint_pair_endpoints R ⟨e, j⟩
      rcases (PushPuzzle.NCL.Strip.Sweep.Arc.pair_eq R (segmentEquiv R ⟨e, j.castSucc⟩)) with hp | hp
      · exact Or.inr ((congrArg Prod.snd hp).symm.trans h)
      · exact Or.inl ((congrArg Prod.snd hp).symm.trans h)
    · refine ⟨rfl, ?_⟩
      have h : ((segmentEquiv R ⟨e, j.succ⟩).pair R).1 = unitPoint R (.inr ⟨e, j⟩) := rfl
      rcases (PushPuzzle.NCL.Strip.Sweep.Arc.pair_eq R (segmentEquiv R ⟨e, j.succ⟩)) with hp | hp
      · exact Or.inl ((congrArg Prod.fst hp).symm.trans h)
      · exact Or.inr ((congrArg Prod.fst hp).symm.trans h)

/-- The actual incoming ports followed by the actual outgoing ports at one grid site. -/
@[expose] def localPorts (es : List E) (p : Point) (w : E → ℕ) : List (WeightedPort (Arc R)) :=
  (slice R es p).incoming.map (fun a => ⟨⟨a, true⟩, w a.edge⟩) ++
    (slice R es p).outgoing.map (fun a => ⟨⟨a, false⟩, w a.edge⟩)

/-- A local weighted port is exactly an actual arc endpoint at that site. -/
theorem mem_localPorts (es : List E) (p : Point) (w : E → ℕ) (q : WeightedPort (Arc R)) :
    q ∈ localPorts R es p w ↔
      q.1.edge.edge ∈ es ∧ q.2 = w q.1.edge.edge ∧ q.1.edge.endpoint R q.1.dir = p := by
  rcases q with ⟨⟨a, d⟩, n⟩
  cases d <;>
    simp [localPorts, mem_slice_incoming, mem_slice_outgoing, PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, eq_comm,
      and_assoc, and_comm, and_left_comm]

/-- Distinct actual local unit arcs give distinct weighted local incidences. -/
private theorem localPorts_nodup {es : List E} (hes : es.Nodup) (p : Point) (w : E → ℕ) :
    (localPorts R es p w).Nodup := by
  rw [localPorts, List.nodup_append]
  refine ⟨?_, ?_, ?_⟩
  · exact ((frontier_nodup R hes _).filter _).map
      (fun _ _ h => congrArg (fun q : WeightedPort (Arc R) => q.1.edge) h)
  · exact ((frontier_nodup R hes _).filter _).map
      (fun _ _ h => congrArg (fun q : WeightedPort (Arc R) => q.1.edge) h)
  · intro q hq q' hq' h
    obtain ⟨a, _, rfl⟩ := List.mem_map.mp hq
    obtain ⟨b, _, rfl⟩ := List.mem_map.mp hq'
    have := congrArg (fun q : WeightedPort (Arc R) => q.1.dir) h
    cases this

private theorem endpoint_decide (a : Arc R) {p : Point}
    (h : a.lower R = p ∨ a.upper R = p) :
    a.endpoint R (decide (a.upper R = p)) = p := by
  rcases h with h | h
  · have hn : a.upper R ≠ p := by
      intro he
      have ht := a.level_lt R
      rw [h, he] at ht
      exact (lt_self_iff_false _).mp ht
    simp [PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, h, hn]
  · simp [PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, h]

private theorem endpoint_dir (a : Arc R) (d : Bool) {p : Point}
    (h : a.endpoint R d = p) : d = decide (a.upper R = p) := by
  cases d
  · have hn : a.upper R ≠ p := by
      intro he
      have ht := a.level_lt R
      change a.lower R = p at h
      rw [h, he] at ht
      exact (lt_self_iff_false _).mp ht
    simp [hn]
  · exact (decide_eq_true_eq.mpr h).symm

/-- Reading a joint's actual local ports in sweep order retains its weighted incidence multiset.
-/
theorem joint_ports_perm [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    {es : List E} (hes : es.Nodup) (j : Subdivision.Joint (jointCount R)) (he : j.1 ∈ es) :
    (unitGraph R G w (.inr j)).ports.Perm
      ((localPorts R es (unitPoint R (.inr j)) w).filter
        (fun q => decide (q.1.edge.edge = j.1))) := by
  let a := segmentEquiv R ⟨j.1, j.2.castSucc⟩
  let b := segmentEquiv R ⟨j.1, j.2.succ⟩
  have hab : a ≠ b := by
    intro h
    have hi := congrArg (fun a : Arc R => a.index.val) h
    change j.2.val = j.2.val + 1 at hi
    omega
  rw [unitGraph_joint]
  apply (List.perm_ext_iff_of_nodup ?_ ((localPorts_nodup R hes _ w).filter _)).mpr
  · intro q
    simp only [List.mem_filter, mem_localPorts, decide_eq_true_eq]
    constructor
    · intro hq
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
      rcases hq with rfl | rfl
      · have ha := (joint_arc_iff R j a).mpr (Or.inl rfl)
        exact ⟨⟨he, rfl, endpoint_decide R a ha.2⟩, rfl⟩
      · have hb := (joint_arc_iff R j b).mpr (Or.inr rfl)
        exact ⟨⟨he, rfl, endpoint_decide R b hb.2⟩, rfl⟩
    · rintro ⟨⟨_, hw, hp⟩, heq⟩
      have hd := endpoint_dir R q.1.edge q.1.dir hp
      have ht : q.1.edge.lower R = unitPoint R (.inr j) ∨
          q.1.edge.upper R = unitPoint R (.inr j) := by
        cases h : q.1.dir
        · exact Or.inl (by simpa only [PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, h, Bool.false_eq_true, ite_false] using hp)
        · exact Or.inr (by simpa only [PushPuzzle.NCL.Strip.Sweep.Arc.endpoint, h, ite_true] using hp)
      have hj := (joint_arc_iff R j q.1.edge).mp ⟨heq, ht⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rcases q with ⟨⟨c, d⟩, n⟩
      rcases hj with rfl | rfl
      · left
        simp only [WeightedPort.mk.injEq, Port.mk.injEq, true_and]
        exact ⟨hd, hw⟩
      · right
        simp only [WeightedPort.mk.injEq, Port.mk.injEq, true_and]
        exact ⟨hd, hw⟩
  · simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, List.nodup_nil, and_true,
      not_false_eq_true]
    intro h
    exact hab (congrArg (fun q : WeightedPort (Arc R) => q.1.edge) h)

/-- The actual joint constraint is exactly its actual slice ports on the same original edge. -/
theorem joint_sat_iff [DecidableEq E] (G : ConstraintGraph V E) (w : E → ℕ)
    {es : List E} (hes : es.Nodup) (j : Subdivision.Joint (jointCount R)) (he : j.1 ∈ es)
    (s : Arc R → Bool) :
    (unitGraph R G w (.inr j)).Sat s ↔
      (Vertex.mk ((localPorts R es (unitPoint R (.inr j)) w).filter
        (fun q => decide (q.1.edge.edge = j.1))) (w j.1)).Sat s :=
  Vertex.sat_iff_of_perm (joint_ports_perm R G w hes j he)
    (by rw [unitGraph_joint]) s

end PushPuzzle.NCL.Strip.Sweep

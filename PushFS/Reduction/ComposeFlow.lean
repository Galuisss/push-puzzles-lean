/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.SegmentFlow

/-! Compose true unit paths at one common endpoint without creating a wire branch. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem neighbor_ne {d : Direction} {p q : GridRouting.Point}
    (h : neighbor d p=some q) : p≠q := by
  intro he
  subst q
  rcases p with ⟨x,y⟩
  cases d <;> simp only [neighbor,Option.some.injEq,Prod.mk.injEq] at h
  · split_ifs at h; simp_all; omega
  · omega
  · omega
  · split_ifs at h; simp_all; omega

theorem HasArc.endpoints {ss : List Segment} {d : Direction} {p : GridRouting.Point} (h : HasArc ss d p) :
    ∃ q,neighbor d p=some q ∧ HasPoint ss p ∧ HasPoint ss q := by
  obtain ⟨s,hs,ha⟩ := h
  obtain ⟨q,hq,hp,ht⟩ := ha.endpoints
  exact ⟨q,hq,⟨s,hs,hp⟩,⟨s,hs,ht⟩⟩

theorem HasArc.point {ss : List Segment} {d : Direction} {p : GridRouting.Point} (h : HasArc ss d p) : HasPoint ss p :=
  h.endpoints.choose_spec.2.1

private theorem HasIncoming.endpoints {ss : List Segment} {d : Direction} {p : GridRouting.Point}
    (h : HasIncoming ss d p) :
    ∃ q,neighbor d p=some q ∧ HasPoint ss p ∧ HasPoint ss q := by
  obtain ⟨q,hq,ha⟩ := h
  obtain ⟨r,hr,hqP,hpP⟩ := ha.endpoints
  have hr' := neighbor_reverse hq
  rw [hr'] at hr
  cases Option.some.inj hr
  exact ⟨q,hq,hpP,hqP⟩

theorem HasIncoming.point {ss : List Segment} {d : Direction} {p : GridRouting.Point} (h : HasIncoming ss d p) : HasPoint ss p :=
  h.endpoints.choose_spec.2.1

@[simp] theorem hasArc_append (ss tt : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasArc (ss++tt) d p ↔ HasArc ss d p ∨ HasArc tt d p := by simp [HasArc,List.mem_append,or_and_right,exists_or]

@[simp] theorem hasPoint_append (ss tt : List Segment) (p : GridRouting.Point) :
    HasPoint (ss++tt) p ↔ HasPoint ss p ∨ HasPoint tt p := by simp [HasPoint,List.mem_append,or_and_right,exists_or]

@[simp] theorem hasIncoming_append (ss tt : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasIncoming (ss++tt) d p ↔ HasIncoming ss d p ∨ HasIncoming tt d p := by
  simp [HasIncoming,and_or_left,exists_or]

/-- Endpoint-only intersection preserves the exact incoming/outgoing unit path contract. -/
theorem UnitFlow.append {ss tt : List Segment} {source joint target : GridRouting.Point}
    (f : UnitFlow ss source joint) (g : UnitFlow tt joint target)
    (hcontact : ∀ p,HasPoint ss p → HasPoint tt p → p=joint) : UnitFlow (ss++tt) source target where
  source_mem := (hasPoint_append _ _ _).mpr (Or.inl f.source_mem)
  target_mem := (hasPoint_append _ _ _).mpr (Or.inr g.target_mem)
  outgoing_unique p d d' h h' := by
    rw [hasArc_append] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact f.outgoing_unique p d d' h h'
    · exact False.elim (((f.outgoing_iff p).mp ⟨d,h⟩).2 (hcontact p h.point h'.point))
    · exact False.elim (((f.outgoing_iff p).mp ⟨d',h'⟩).2 (hcontact p h'.point h.point))
    · exact g.outgoing_unique p d d' h h'
  incoming_unique p d d' h h' := by
    rw [hasIncoming_append] at h h'
    rcases h with h | h <;> rcases h' with h' | h'
    · exact f.incoming_unique p d d' h h'
    · exact False.elim (((g.incoming_iff p).mp ⟨d',h'⟩).2 (hcontact p h.point h'.point))
    · exact False.elim (((g.incoming_iff p).mp ⟨d,h⟩).2 (hcontact p h'.point h.point))
    · exact g.incoming_unique p d d' h h'
  outgoing_iff p := by
    constructor
    · rintro ⟨d,ha⟩
      rw [hasArc_append] at ha
      rcases ha with ha | ha
      · refine ⟨(hasPoint_append _ _ _).mpr (Or.inl ha.point),?_⟩
        intro he
        have hp : HasPoint tt p := he.symm ▸ g.target_mem
        exact ((f.outgoing_iff p).mp ⟨d,ha⟩).2 (hcontact p ha.point hp)
      · exact ⟨(hasPoint_append _ _ _).mpr (Or.inr ha.point),((g.outgoing_iff p).mp ⟨d,ha⟩).2⟩
    · rintro ⟨hp,hne⟩
      rw [hasPoint_append] at hp
      rcases hp with hp | hp
      · by_cases he : p=joint
        · have hp' : HasPoint tt p := he.symm ▸ g.source_mem
          obtain ⟨d,hd⟩ := (g.outgoing_iff p).mpr ⟨hp',hne⟩
          exact ⟨d,(hasArc_append _ _ _ _).mpr (Or.inr hd)⟩
        · obtain ⟨d,hd⟩ := (f.outgoing_iff p).mpr ⟨hp,he⟩
          exact ⟨d,(hasArc_append _ _ _ _).mpr (Or.inl hd)⟩
      · obtain ⟨d,hd⟩ := (g.outgoing_iff p).mpr ⟨hp,hne⟩
        exact ⟨d,(hasArc_append _ _ _ _).mpr (Or.inr hd)⟩
  incoming_iff p := by
    constructor
    · rintro ⟨d,ha⟩
      rw [hasIncoming_append] at ha
      rcases ha with ha | ha
      · exact ⟨(hasPoint_append _ _ _).mpr (Or.inl ha.point),((f.incoming_iff p).mp ⟨d,ha⟩).2⟩
      · refine ⟨(hasPoint_append _ _ _).mpr (Or.inr ha.point),?_⟩
        intro he
        have hp : HasPoint ss p := he.symm ▸ f.source_mem
        exact ((g.incoming_iff p).mp ⟨d,ha⟩).2 (hcontact p hp ha.point)
    · rintro ⟨hp,hne⟩
      rw [hasPoint_append] at hp
      rcases hp with hp | hp
      · obtain ⟨d,hd⟩ := (f.incoming_iff p).mpr ⟨hp,hne⟩
        exact ⟨d,(hasIncoming_append _ _ _ _).mpr (Or.inl hd)⟩
      · by_cases he : p=joint
        · have hp' : HasPoint ss p := he.symm ▸ f.target_mem
          obtain ⟨d,hd⟩ := (f.incoming_iff p).mpr ⟨hp',hne⟩
          exact ⟨d,(hasIncoming_append _ _ _ _).mpr (Or.inl hd)⟩
        · obtain ⟨d,hd⟩ := (g.incoming_iff p).mpr ⟨hp,he⟩
          exact ⟨d,(hasIncoming_append _ _ _ _).mpr (Or.inr hd)⟩
  no_uturn p d hi ho := by
    rw [hasIncoming_append] at hi
    rw [hasArc_append] at ho
    rcases hi with hi | hi <;> rcases ho with ho | ho
    · exact f.no_uturn p d hi ho
    · obtain ⟨q,hq,hpA,hqA⟩ := hi.endpoints
      obtain ⟨r,hr,hpB,hrB⟩ := ho.endpoints
      have hqr := Option.some.inj (hq.symm.trans hr)
      subst r
      have hp := hcontact p hpA hpB
      have hq' := hcontact q hqA hrB
      exact neighbor_ne hq (hp.trans hq'.symm)
    · exact ((f.outgoing_iff p).mp ⟨d,ho⟩).2 (hcontact p ho.point hi.point)
    · exact g.no_uturn p d hi ho

/-- Endpoint row bounds and the next piece's true top fiber discharge the physical path contact. -/
theorem UnitFlow.append_at_row {ss tt : List Segment} {source joint target : GridRouting.Point}
    (f : UnitFlow ss source joint) (g : UnitFlow tt joint target)
    (hs : Connects ss source joint) (ht : Connects tt joint target)
    (hunique : ∀ p,HasPoint tt p → p.2=joint.2 → p=joint) : UnitFlow (ss++tt) source target := by
  apply f.append g
  intro p hp hq
  have hpB := hs.row_bounds hp
  have hqB := ht.row_bounds hq
  exact hunique p hq (by omega)

end PushPuzzle.PushFS.Reduction

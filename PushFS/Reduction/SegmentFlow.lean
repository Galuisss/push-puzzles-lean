/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.BandFlow

/-! Exact unit flow on one actual aligned segment, including degenerate joins. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

def Segment.reversed (s : Segment) : Segment := ⟨s.finish,s.start⟩

@[simp] theorem Segment.reversed_start (s : Segment) : s.reversed.start=s.finish := rfl
@[simp] theorem Segment.reversed_finish (s : Segment) : s.reversed.finish=s.start := rfl

theorem Segment.reverse_contains (s : Segment) (p : GridRouting.Point) : s.reversed.Contains p ↔ s.Contains p := by
  dsimp [Segment.reversed,Segment.Contains]
  omega

theorem Segment.arc_reverse_step (s : Segment) {d : Direction} {p q : GridRouting.Point}
    (hn : neighbor d p=some q) : s.Arc d.opposite q ↔ s.reversed.Arc d p := by
  cases d <;> dsimp only [neighbor,Direction.opposite,Segment.reversed,Segment.Arc] at hn ⊢
  · split_ifs at hn; simp_all [Prod.ext_iff]; omega
  · simp only [Option.some.injEq,Prod.ext_iff] at hn
    omega
  · simp only [Option.some.injEq,Prod.ext_iff] at hn
    omega
  · split_ifs at hn; simp_all [Prod.ext_iff]; omega

theorem Segment.incoming_reversed (s : Segment) (d : Direction) (p : GridRouting.Point) :
    (∃ q,neighbor d p=some q ∧ s.Arc d.opposite q) ↔ s.reversed.Arc d p := by
  constructor
  · rintro ⟨q,hn,ha⟩
    exact (s.arc_reverse_step hn).mp ha
  · intro ha
    obtain ⟨q,hn,_,_⟩ := ha.endpoints
    exact ⟨q,hn,(s.arc_reverse_step hn).mpr ha⟩

@[simp] theorem hasArc_singleton (s : Segment) (d : Direction) (p : GridRouting.Point) :
    HasArc [s] d p ↔ s.Arc d p := by simp [HasArc]

@[simp] theorem hasPoint_singleton (s : Segment) (p : GridRouting.Point) :
    HasPoint [s] p ↔ s.Contains p := by simp [HasPoint]

@[simp] theorem hasIncoming_singleton (s : Segment) (d : Direction) (p : GridRouting.Point) :
    HasIncoming [s] d p ↔ s.reversed.Arc d p := by
  simp only [HasIncoming,hasArc_singleton]
  exact s.incoming_reversed d p

private theorem Segment.arc_direction_unique (s : Segment) (p : GridRouting.Point)
    {d d' : Direction}
    (h : s.Arc d p) (h' : s.Arc d' p) : d=d' := by
  cases d <;> cases d'
  all_goals first | rfl | simp only [Segment.Arc] at h h'
  all_goals omega

private theorem Segment.Arc.ne_finish {s : Segment} {d : Direction} {p : GridRouting.Point}
    (h : s.Arc d p) : p≠s.finish := by
  intro he
  subst p
  cases d <;> simp only [Segment.Arc] at h <;> omega

theorem Segment.outgoing_iff (s : Segment) (p : GridRouting.Point) :
    (∃ d,s.Arc d p) ↔ s.Contains p ∧ p≠s.finish := by
  constructor
  · rintro ⟨d,ha⟩
    obtain ⟨_,_,hp,_⟩ := ha.endpoints
    exact ⟨hp,ha.ne_finish⟩
  · rintro ⟨hp,hne⟩
    have hne' : ¬(p.1=s.finish.1 ∧ p.2=s.finish.2) := fun hh => hne (Prod.ext hh.1 hh.2)
    rcases hp with hp | hp
    · by_cases hh : s.start.2≤s.finish.2
      · refine ⟨.south,?_,?_,?_,?_⟩
        all_goals omega
      · refine ⟨.north,?_,?_,?_,?_⟩
        all_goals omega
    · by_cases hh : s.start.1≤s.finish.1
      · refine ⟨.east,?_,?_,?_,?_⟩
        all_goals omega
      · refine ⟨.west,?_,?_,?_,?_⟩
        all_goals omega

/-- Every actual horizontal or vertical instruction is a complete directed unit path. -/
theorem Segment.unitFlow (s : Segment) (ha : s.AxisAligned) : UnitFlow [s] s.start s.finish where
  source_mem := ⟨s,by simp,Segment.contains_of_bounds ha ⟨min_le_left _ _,le_max_left _ _,min_le_left _ _,le_max_left _ _⟩⟩
  target_mem := ⟨s,by simp,Segment.contains_of_bounds ha ⟨min_le_right _ _,le_max_right _ _,min_le_right _ _,le_max_right _ _⟩⟩
  outgoing_unique p d d' h h' := s.arc_direction_unique p ((hasArc_singleton _ _ _).mp h) ((hasArc_singleton _ _ _).mp h')
  incoming_unique p d d' h h' := s.reversed.arc_direction_unique p
    ((hasIncoming_singleton _ _ _).mp h) ((hasIncoming_singleton _ _ _).mp h')
  outgoing_iff p := by simpa only [hasArc_singleton,hasPoint_singleton] using s.outgoing_iff p
  incoming_iff p := by
    simpa only [hasIncoming_singleton,hasPoint_singleton,Segment.reverse_contains,Segment.reversed_finish]
      using s.reversed.outgoing_iff p
  no_uturn p d hi ho := by
    rw [hasIncoming_singleton] at hi
    rw [hasArc_singleton] at ho
    cases d <;> dsimp [Segment.reversed,Segment.Arc] at hi ho <;> omega

end PushPuzzle.PushFS.Reduction

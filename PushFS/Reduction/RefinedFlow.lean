/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.RefinedArcs

/-! Sixteen-fold refinement preserves ordinary directed wires at every new intermediate pixel. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem no_opposing_horizontal {ss : List Segment} {source target : GridRouting.Point}
    (f : UnitFlow ss source target) {s t : Segment} (hs : s∈ss) (ht : t∈ss) {p : GridRouting.Point}
    (he : s.refined.Arc .east p) (hw : t.refined.Arc .west p) : False := by
  dsimp [Segment.refined,refinePoint,Segment.Arc] at he hw
  by_cases hst : s.start.1<t.start.1
  · let q : GridRouting.Point := (max s.start.1 t.finish.1,s.start.2)
    have hE : s.Arc .east q := by dsimp [Segment.Arc,q]; omega
    have hW : t.Arc .west (q.1+1,q.2) := by dsimp [Segment.Arc,q]; omega
    exact f.no_uturn q .east ⟨(q.1+1,q.2),rfl,t,ht,hW⟩ ⟨s,hs,hE⟩
  · have hE : s.Arc .east (s.start.1,s.start.2) := by dsimp [Segment.Arc]; omega
    have hW : t.Arc .west (s.start.1,s.start.2) := by dsimp [Segment.Arc]; omega
    have hd := f.outgoing_unique _ .east .west ⟨s,hs,hE⟩ ⟨t,ht,hW⟩
    cases hd

private theorem no_opposing_vertical {ss : List Segment} {source target : GridRouting.Point}
    (f : UnitFlow ss source target) {s t : Segment} (hs : s∈ss) (ht : t∈ss) {p : GridRouting.Point}
    (hso : s.refined.Arc .south p) (hno : t.refined.Arc .north p) : False := by
  dsimp [Segment.refined,refinePoint,Segment.Arc] at hso hno
  by_cases hst : s.start.2<t.start.2
  · let q : GridRouting.Point := (s.start.1,max s.start.2 t.finish.2)
    have hS : s.Arc .south q := by dsimp [Segment.Arc,q]; omega
    have hN : t.Arc .north (q.1,q.2+1) := by dsimp [Segment.Arc,q]; omega
    exact f.no_uturn q .south ⟨(q.1,q.2+1),rfl,t,ht,hN⟩ ⟨s,hs,hS⟩
  · have hS : s.Arc .south (s.start.1,s.start.2) := by dsimp [Segment.Arc]; omega
    have hN : t.Arc .north (s.start.1,s.start.2) := by dsimp [Segment.Arc]; omega
    have hd := f.outgoing_unique _ .south .north ⟨s,hs,hS⟩ ⟨t,ht,hN⟩
    cases hd

private theorem UnitFlow.refined_outgoing_unique {ss : List Segment}
    {source target : GridRouting.Point}
    (f : UnitFlow ss source target) (p : GridRouting.Point) {d d' : Direction}
    (h : HasArc (ss.map Segment.refined) d p) (h' : HasArc (ss.map Segment.refined) d' p) : d=d' := by
  obtain ⟨r,hr,ha⟩ := h
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨r,hr,hb⟩ := h'
  obtain ⟨t,ht,rfl⟩ := List.mem_map.mp hr
  cases d <;> cases d'
  · rfl
  · obtain ⟨q,hq,hq'⟩ := Segment.refined_cross (Or.inl rfl) (Or.inl rfl) ha hb
    exact f.outgoing_unique q .north .east ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · exact False.elim (no_opposing_vertical f ht hs hb ha)
  · obtain ⟨q,hq,hq'⟩ := Segment.refined_cross (Or.inl rfl) (Or.inr rfl) ha hb
    exact f.outgoing_unique q .north .west ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · obtain ⟨q,hq',hq⟩ := Segment.refined_cross (Or.inl rfl) (Or.inl rfl) hb ha
    exact f.outgoing_unique q .east .north ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · rfl
  · obtain ⟨q,hq',hq⟩ := Segment.refined_cross (Or.inr rfl) (Or.inl rfl) hb ha
    exact f.outgoing_unique q .east .south ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · exact False.elim (no_opposing_horizontal f hs ht ha hb)
  · exact False.elim (no_opposing_vertical f hs ht ha hb)
  · obtain ⟨q,hq,hq'⟩ := Segment.refined_cross (Or.inr rfl) (Or.inl rfl) ha hb
    exact f.outgoing_unique q .south .east ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · rfl
  · obtain ⟨q,hq,hq'⟩ := Segment.refined_cross (Or.inr rfl) (Or.inr rfl) ha hb
    exact f.outgoing_unique q .south .west ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · obtain ⟨q,hq',hq⟩ := Segment.refined_cross (Or.inl rfl) (Or.inr rfl) hb ha
    exact f.outgoing_unique q .west .north ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · exact False.elim (no_opposing_horizontal f ht hs hb ha)
  · obtain ⟨q,hq',hq⟩ := Segment.refined_cross (Or.inr rfl) (Or.inr rfl) hb ha
    exact f.outgoing_unique q .west .south ⟨s,hs,hq⟩ ⟨t,ht,hq'⟩
  · rfl

private theorem UnitFlow.refined_no_uturn {ss : List Segment} {source target : GridRouting.Point}
    (f : UnitFlow ss source target) (p : GridRouting.Point) (d : Direction)
    (hi : HasIncoming (ss.map Segment.refined) d p) (ho : HasArc (ss.map Segment.refined) d p) : False := by
  have hi' := (hasIncoming_reversed (ss.map Segment.refined) d p).mp hi
  rw [map_reversed_refined] at hi'
  obtain ⟨r,hr,hrev⟩ := hi'
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
  obtain ⟨t,ht0,rfl⟩ := List.mem_map.mp hu
  obtain ⟨r,hr,hfor⟩ := ho
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨q,hq,hq'⟩ := Segment.refined_shared_arc hfor hrev
  have hin : HasIncoming ss d q := (hasIncoming_reversed ss d q).mpr
    ⟨t.reversed,List.mem_map.mpr ⟨t,ht0,rfl⟩,hq'⟩
  exact f.no_uturn q d hin ⟨s,hs,hq⟩

private theorem UnitFlow.refined_outgoing_iff {ss : List Segment}
    {source target : GridRouting.Point}
    (f : UnitFlow ss source target) (p : GridRouting.Point) :
    (∃ d,HasArc (ss.map Segment.refined) d p) ↔ HasPoint (ss.map Segment.refined) p ∧ p≠refinePoint target := by
  constructor
  · rintro ⟨d,ha⟩
    refine ⟨ha.point,?_⟩
    intro he
    subst p
    have hOld := (hasArc_refined_anchor ss d target).mp ha
    exact ((f.outgoing_iff target).mp ⟨d,hOld⟩).2 rfl
  · rintro ⟨⟨r,hr,hp⟩,hne⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    by_cases he : p=refinePoint s.finish
    · have hp' : HasPoint ss s.finish := ⟨s,hs,(s.refined_anchor s.finish).mp (by simpa only [he] using hp)⟩
      have hn : s.finish≠target := fun hh=>hne (he.trans (congrArg refinePoint hh))
      obtain ⟨d,hd⟩ := (f.outgoing_iff s.finish).mpr ⟨hp',hn⟩
      refine ⟨d,?_⟩
      rw [he]
      exact (hasArc_refined_anchor ss d s.finish).mpr hd
    · have hn : p≠s.refined.finish := by simpa only [Segment.refined_finish] using he
      obtain ⟨d,ha⟩ := (s.refined.outgoing_iff p).mpr ⟨hp,hn⟩
      exact ⟨d,s.refined,List.mem_map.mpr ⟨s,hs,rfl⟩,ha⟩

private theorem UnitFlow.refined_incoming_iff {ss : List Segment}
    {source target : GridRouting.Point}
    (f : UnitFlow ss source target) (p : GridRouting.Point) :
    (∃ d,HasIncoming (ss.map Segment.refined) d p) ↔ HasPoint (ss.map Segment.refined) p ∧ p≠refinePoint source := by
  constructor
  · rintro ⟨d,hi⟩
    have ha := (hasIncoming_reversed (ss.map Segment.refined) d p).mp hi
    rw [map_reversed_refined] at ha
    obtain ⟨hp,hne⟩ := (f.reversed.refined_outgoing_iff p).mp ⟨d,ha⟩
    rw [← map_reversed_refined] at hp
    exact ⟨(hasPoint_reversed (ss.map Segment.refined) p).mp hp,hne⟩
  · rintro ⟨hp,hne⟩
    have hp' := (hasPoint_reversed (ss.map Segment.refined) p).mpr hp
    rw [map_reversed_refined] at hp'
    obtain ⟨d,ha⟩ := (f.reversed.refined_outgoing_iff p).mpr ⟨hp',hne⟩
    refine ⟨d,(hasIncoming_reversed (ss.map Segment.refined) d p).mpr ?_⟩
    rw [map_reversed_refined]
    exact ha

/-- Ordinary unit flow is retained at every new grid pixel, including between old lattice anchors. -/
theorem UnitFlow.refined {ss : List Segment} {source target : GridRouting.Point} (f : UnitFlow ss source target) :
    UnitFlow (ss.map Segment.refined) (refinePoint source) (refinePoint target) where
  source_mem := (hasPoint_refined_anchor ss source).mpr f.source_mem
  target_mem := (hasPoint_refined_anchor ss target).mpr f.target_mem
  outgoing_unique p _ _ := f.refined_outgoing_unique p
  incoming_unique p d d' h h' := by
    apply f.reversed.refined_outgoing_unique p
    · rw [← map_reversed_refined]
      exact (hasIncoming_reversed (ss.map Segment.refined) d p).mp h
    · rw [← map_reversed_refined]
      exact (hasIncoming_reversed (ss.map Segment.refined) d' p).mp h'
  outgoing_iff := f.refined_outgoing_iff
  incoming_iff := f.refined_incoming_iff
  no_uturn := f.refined_no_uturn

end PushPuzzle.PushFS.Reduction

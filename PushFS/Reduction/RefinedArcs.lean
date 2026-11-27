/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.ReverseFlow

/-! Exact unit-arc transport and overlap witnesses for the actual sixteen-fold refinement. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

@[simp] theorem Segment.refined_start (s : Segment) : s.refined.start=refinePoint s.start := rfl
@[simp] theorem Segment.refined_finish (s : Segment) : s.refined.finish=refinePoint s.finish := rfl

theorem Segment.refined_arc_anchor (s : Segment) (d : Direction) (p : GridRouting.Point) :
    s.refined.Arc d (refinePoint p) ↔ s.Arc d p := by
  cases d <;> dsimp [Segment.refined,refinePoint,Segment.Arc] <;> omega

/-- Shared same-direction refined unit arcs always contain a shared old directed unit arc. -/
theorem Segment.refined_shared_arc {s t : Segment} {d : Direction} {p : GridRouting.Point}
    (hs : s.refined.Arc d p) (ht : t.refined.Arc d p) : ∃ q,s.Arc d q ∧ t.Arc d q := by
  cases d
  · refine ⟨(s.start.1,min s.start.2 t.start.2),?_,?_⟩ <;>
      dsimp [Segment.refined,refinePoint,Segment.Arc] at hs ht ⊢ <;> omega
  · refine ⟨(max s.start.1 t.start.1,s.start.2),?_,?_⟩ <;>
      dsimp [Segment.refined,refinePoint,Segment.Arc] at hs ht ⊢ <;> omega
  · refine ⟨(s.start.1,max s.start.2 t.start.2),?_,?_⟩ <;>
      dsimp [Segment.refined,refinePoint,Segment.Arc] at hs ht ⊢ <;> omega
  · refine ⟨(min s.start.1 t.start.1,s.start.2),?_,?_⟩ <;>
      dsimp [Segment.refined,refinePoint,Segment.Arc] at hs ht ⊢ <;> omega

/-- Crossing vertical and horizontal refined arcs meet at an actual old lattice anchor. -/
theorem Segment.refined_cross {s t : Segment} {d d' : Direction} {p : GridRouting.Point}
    (hd : d=.north ∨ d=.south) (hd' : d'=.east ∨ d'=.west)
    (hs : s.refined.Arc d p) (ht : t.refined.Arc d' p) : ∃ q,s.Arc d q ∧ t.Arc d' q := by
  rcases hd with rfl | rfl <;> rcases hd' with rfl | rfl
  all_goals
    refine ⟨(s.start.1,t.start.2),?_,?_⟩ <;>
      dsimp [Segment.refined,refinePoint,Segment.Arc] at hs ht ⊢ <;> omega

theorem hasArc_refined_anchor (ss : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasArc (ss.map Segment.refined) d (refinePoint p) ↔ HasArc ss d p := by
  constructor
  · rintro ⟨r,hr,ha⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact ⟨s,hs,(s.refined_arc_anchor d p).mp ha⟩
  · rintro ⟨s,hs,ha⟩
    exact ⟨s.refined,List.mem_map.mpr ⟨s,hs,rfl⟩,(s.refined_arc_anchor d p).mpr ha⟩

theorem hasPoint_refined_anchor (ss : List Segment) (p : GridRouting.Point) :
    HasPoint (ss.map Segment.refined) (refinePoint p) ↔ HasPoint ss p := by
  constructor
  · rintro ⟨r,hr,ha⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact ⟨s,hs,(s.refined_anchor p).mp ha⟩
  · rintro ⟨s,hs,ha⟩
    exact ⟨s.refined,List.mem_map.mpr ⟨s,hs,rfl⟩,(s.refined_anchor p).mpr ha⟩

theorem map_reversed_refined (ss : List Segment) :
    (ss.map Segment.refined).map Segment.reversed=(ss.map Segment.reversed).map Segment.refined := by
  simp only [List.map_map]
  rfl

theorem hasIncoming_refined_anchor (ss : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasIncoming (ss.map Segment.refined) d (refinePoint p) ↔ HasIncoming ss d p := by
  rw [hasIncoming_reversed,map_reversed_refined,hasArc_refined_anchor,← hasIncoming_reversed]

end PushPuzzle.PushFS.Reduction

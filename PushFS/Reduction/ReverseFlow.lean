/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.TranslateFlow

/-! Reversing every actual directed instruction exchanges incoming and outgoing unit flow. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

@[simp] theorem Segment.reversed_reversed (s : Segment) : s.reversed.reversed=s := rfl

@[simp] theorem map_reversed_reversed (ss : List Segment) :
    (ss.map Segment.reversed).map Segment.reversed=ss := by
  simp only [List.map_map,Function.comp_def,Segment.reversed_reversed,List.map_id']

theorem hasPoint_reversed (ss : List Segment) (p : GridRouting.Point) :
    HasPoint (ss.map Segment.reversed) p ↔ HasPoint ss p := by
  constructor
  · rintro ⟨r,hr,hp⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    exact ⟨s,hs,(s.reverse_contains p).mp hp⟩
  · rintro ⟨s,hs,hp⟩
    exact ⟨s.reversed,List.mem_map.mpr ⟨s,hs,rfl⟩,(s.reverse_contains p).mpr hp⟩

theorem hasIncoming_reversed_list (ss : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasIncoming (ss.map Segment.reversed) d p ↔ HasArc ss d p := by
  rw [hasIncoming_reversed,map_reversed_reversed]

theorem UnitFlow.reversed {ss : List Segment} {source target : GridRouting.Point} (f : UnitFlow ss source target) :
    UnitFlow (ss.map Segment.reversed) target source where
  source_mem := (hasPoint_reversed ss target).mpr f.target_mem
  target_mem := (hasPoint_reversed ss source).mpr f.source_mem
  outgoing_unique p d d' h h' := f.incoming_unique p d d'
    ((hasIncoming_reversed ss d p).mpr h) ((hasIncoming_reversed ss d' p).mpr h')
  incoming_unique p d d' h h' := f.outgoing_unique p d d'
    ((hasIncoming_reversed_list ss d p).mp h) ((hasIncoming_reversed_list ss d' p).mp h')
  outgoing_iff p := by
    simpa only [hasIncoming_reversed,hasPoint_reversed] using f.incoming_iff p
  incoming_iff p := by
    simpa only [hasIncoming_reversed_list,hasPoint_reversed] using f.outgoing_iff p
  no_uturn p d hi ho := f.no_uturn p d ((hasIncoming_reversed ss d p).mpr ho)
    ((hasIncoming_reversed_list ss d p).mp hi)

end PushPuzzle.PushFS.Reduction

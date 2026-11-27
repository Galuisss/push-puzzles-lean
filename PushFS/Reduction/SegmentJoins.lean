/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PathData
import Mathlib.Data.List.Chain

/-! Serialized actual paths retain their literal first endpoint, last endpoint and every internal join. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

private theorem segments_nonempty {p q : GridRouting.Point}
    (r : GridRouting.Path p q) : segments r≠[] := by
  induction r with
  | horizontal => simp [segments]
  | vertical => simp [segments]
  | comp r t ihr _ =>
    intro he
    exact ihr (List.append_eq_nil_iff.mp he).1

private theorem segments_head {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    (segments r).head?.map Segment.start=some p := by
  induction r with
  | horizontal => rfl
  | vertical => rfl
  | comp r t ihr _ =>
    rw [segments,List.head?_append_of_ne_nil _ (segments_nonempty r)]
    exact ihr

private theorem segments_last {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    (segments r).getLast?.map Segment.finish=some q := by
  induction r with
  | horizontal => rfl
  | vertical => rfl
  | comp r t _ iht =>
    rw [segments,List.getLast?_append_of_ne_nil _ (segments_nonempty t)]
    exact iht

private theorem segments_chain {p q : GridRouting.Point} (r : GridRouting.Path p q) :
    (segments r).IsChain (fun s t=>s.finish=t.start) := by
  induction r with
  | horizontal => simp [segments]
  | vertical => simp [segments]
  | @comp p q u r t ihr iht =>
    apply ihr.append iht
    intro s hs v hv
    have he := segments_last r
    have hf := segments_head t
    rw [Option.mem_def.mp hs,Option.map_some,Option.some.injEq] at he
    rw [Option.mem_def.mp hv,Option.map_some,Option.some.injEq] at hf
    exact he.trans hf.symm

private theorem Connects.head {ss : List Segment} {p q : GridRouting.Point} (h : Connects ss p q) :
    ss.head?.map Segment.start=some p := by obtain ⟨r,rfl⟩:=h; exact segments_head r

private theorem Connects.last {ss : List Segment} {p q : GridRouting.Point} (h : Connects ss p q) :
    ss.getLast?.map Segment.finish=some q := by obtain ⟨r,rfl⟩:=h; exact segments_last r

private theorem Connects.chain {ss : List Segment} {p q : GridRouting.Point} (h : Connects ss p q) :
    ss.IsChain (fun s t=>s.finish=t.start) := by obtain ⟨r,rfl⟩:=h; exact segments_chain r

theorem Connects.endpoints_unique {ss : List Segment} {p q p' q' : GridRouting.Point}
    (h : Connects ss p q) (h' : Connects ss p' q') : p=p' ∧ q=q' :=
  ⟨Option.some.inj (h.head.symm.trans h'.head),Option.some.inj (h.last.symm.trans h'.last)⟩

/-- A serialized whole path determines the literal common endpoint of two separately interpreted fragments. -/
theorem Connects.append_contact {ss tt : List Segment} {p q ps qs pt qt : GridRouting.Point}
    (h : Connects (ss++tt) p q) (hs : Connects ss ps qs) (ht : Connects tt pt qt) : qs=pt := by
  obtain ⟨s,hsm,hse⟩ := Option.map_eq_some_iff.mp hs.last
  obtain ⟨t,htm,hte⟩ := Option.map_eq_some_iff.mp ht.head
  have he := (List.isChain_append.mp h.chain).2.2 s (by simp [hsm]) t (by simp [htm])
  exact hse.symm.trans (he.trans hte)

end PushPuzzle.PushFS.Reduction

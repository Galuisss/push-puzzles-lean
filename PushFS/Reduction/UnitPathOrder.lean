/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.UnitPaths
public import Mathlib.Data.Fin.Tuple.Basic

/-! Finite, injective unit-pixel order extracted from the actual complete directed source path. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


namespace DirectedPath
variable {α : Type} {R : α→α→Prop} {a b : α}

structure Sequence (R : α→α→Prop) (a b : α) where
  length : ℕ
  node : Fin (length+1)→α
  first : node 0=a
  last : node (Fin.last length)=b
  step : ∀i : Fin length,R (node i.castSucc) (node i.succ)

theorem nonempty_of_reach (hr : Relation.ReflTransGen R a b) : Nonempty (Sequence R a b) := by
  induction hr with
  | refl=>exact ⟨⟨0,fun _=>a,rfl,rfl,Fin.elim0⟩⟩
  | @tail c d _ hcd ih=>
    obtain ⟨s⟩:=ih
    refine ⟨⟨s.length+1,Fin.snoc (α:=fun _=>α) s.node d,?_,?_,?_⟩⟩
    · change Fin.snoc (α:=fun _=>α) s.node d ((0 : Fin (s.length+1)).castSucc)=a
      rw [Fin.snoc_castSucc]
      exact s.first
    · exact Fin.snoc_last (α:=fun _=>α) (p:=s.node) (x:=d)
    · intro i
      refine Fin.lastCases ?_ (fun j=>?_) i
      · change R (Fin.snoc (α:=fun _=>α) s.node d (Fin.last s.length).castSucc)
          (Fin.snoc (α:=fun _=>α) s.node d (Fin.last (s.length+1)))
        simpa only [Fin.snoc_castSucc,Fin.snoc_last,s.last] using hcd
      · simpa only [←Fin.castSucc_succ,Fin.snoc_castSucc] using s.step j

/-- Unique predecessors and the genuine initial endpoint exclude every repetition in the extracted order. -/
theorem Sequence.injective (s : Sequence R a b)
    (hleft : ∀{p q r},R p r→R q r→p=q) (hstart : ∀p,¬R p a) : Function.Injective s.node := by
  intro i
  induction i using Fin.induction with
  | zero=>
    intro j
    refine Fin.cases (fun _=>rfl) (fun k he=>?_) j
    have hk:=s.step k
    rw [←he,s.first] at hk
    exact (hstart _ hk).elim
  | succ i ih=>
    intro j
    refine Fin.cases (fun he=>?_) (fun k he=>?_) j
    · have hh:=s.step i
      rw [he,s.first] at hh
      exact (hstart _ hh).elim
    · have hp:=hleft (he ▸s.step i) (s.step k)
      have hi:=ih hp
      exact congrArg Fin.succ (Fin.castSucc_inj.mp hi)

/-- Unique successors and the genuine terminal endpoint put every reachable pixel in the same finite order. -/
theorem Sequence.covers (s : Sequence R a b)
    (hright : ∀{p q r},R p q→R p r→q=r) (hfinish : ∀p,¬R b p)
    {x : α} (hr : Relation.ReflTransGen R a x) : ∃i,s.node i=x := by
  induction hr with
  | refl=>exact ⟨0,s.first⟩
  | @tail c d _ hcd ih=>
    obtain ⟨i,hi⟩:=ih
    by_cases he : i.val=s.length
    · have he' : i=Fin.last s.length:=Fin.ext he
      have hh:=hi.symm ▸hcd
      rw [he',s.last] at hh
      exact (hfinish _ hh).elim
    · let j : Fin s.length:=⟨i.val,by have :=i.isLt; omega⟩
      have he' : j.castSucc=i:=Fin.ext rfl
      exact ⟨j.succ,(hright (s.step j) (he'.symm ▸hi.symm ▸hcd))⟩

theorem Sequence.step_index (s : Sequence R a b) (hinj : Function.Injective s.node)
    (hright : ∀{p q r},R p q→R p r→q=r) (hfinish : ∀p,¬R b p)
    (i j : Fin (s.length+1)) (h : R (s.node i) (s.node j)) : j.val=i.val+1 := by
  by_cases he : i.val=s.length
  · have he' : i=Fin.last s.length:=Fin.ext he
    rw [he',s.last] at h
    exact (hfinish _ h).elim
  · let k : Fin s.length:=⟨i.val,by have :=i.isLt; omega⟩
    have hk : k.castSucc=i:=Fin.ext rfl
    have hh:=hright (s.step k) (hk.symm ▸h)
    have hj:=hinj hh
    exact (congrArg Fin.val hj).symm

end DirectedPath

open Cslib.Complexity.NCL

private theorem UnitReach.mono_arcs {ss tt : List Segment} {p q : GridRouting.Point}
    (hr : UnitReach ss p q) (hm : ∀d p,HasArc ss d p→HasArc tt d p) : UnitReach tt p q := by
  induction hr with
  | refl=>exact .refl
  | tail _ hs ih=>
    obtain ⟨d,ha,hn⟩:=hs
    exact ih.tail ⟨d,hm d _ ha,hn⟩

private theorem path_point_unitReach {p q : GridRouting.Point} (r : GridRouting.Path p q)
    {u : GridRouting.Point} (hu : r.Contains u) : UnitReach (segments r) p u := by
  induction r with
  | horizontal x x' y=>
    have hh:=path_unitReach (GridRouting.Path.horizontal x u.1 y)
    have hr:=hh.mono_arcs (tt:=segments (GridRouting.Path.horizontal x x' y)) (fun d p ha=>by
      obtain ⟨s,hs,ha⟩:=ha
      cases List.mem_singleton.mp hs
      refine ⟨⟨(x,y),(x',y)⟩,List.mem_singleton_self _,?_⟩
      cases d <;> dsimp only [Segment.Arc] at ha ⊢ <;> dsimp only [GridRouting.Path.Contains] at hu <;> omega)
    exact hu.1 ▸hr
  | vertical x y y' hy=>
    have hh:=path_unitReach (GridRouting.Path.vertical x y u.2 hu.2.1)
    have hr:=hh.mono_arcs (tt:=segments (GridRouting.Path.vertical x y y' hy)) (fun d p ha=>by
      obtain ⟨s,hs,ha⟩:=ha
      cases List.mem_singleton.mp hs
      refine ⟨⟨(x,y),(x,y')⟩,List.mem_singleton_self _,?_⟩
      cases d <;> dsimp only [Segment.Arc] at ha ⊢ <;> dsimp only [GridRouting.Path.Contains] at hu <;> omega)
    exact hu.1 ▸hr
  | comp r t ihr iht=>
    rcases hu with hu|hu
    · exact (ihr hu).mono (fun _ hs=>List.mem_append_left _ hs)
    · exact ((path_unitReach r).mono (fun _ hs=>List.mem_append_left _ hs)).trans
        ((iht hu).mono (fun _ hs=>List.mem_append_right _ hs))

/-- Every actual support pixel occurs after the source in the emitted directed order. -/
theorem Connects.point_unitReach {ss : List Segment} {p q u : GridRouting.Point} (hc : Connects ss p q)
    (hu : HasPoint ss u) : UnitReach ss p u := by
  obtain ⟨r,rfl⟩:=hc
  exact path_point_unitReach r ((mem_segments_iff r u).mp hu)

theorem UnitStep.left_mem {ss : List Segment} {p q : GridRouting.Point} (h : UnitStep ss p q) : HasPoint ss p := by
  obtain ⟨d,⟨s,hs,ha⟩,_⟩:=h
  exact ⟨s,hs,ha.endpoints.choose_spec.2.1⟩

theorem UnitStep.right_mem {ss : List Segment} {p q : GridRouting.Point} (h : UnitStep ss p q) : HasPoint ss q := by
  obtain ⟨d,⟨s,hs,ha⟩,hn⟩:=h
  obtain ⟨r,hr,_,ht⟩:=ha.endpoints
  have he : r=q:=Option.some.inj (hr.symm.trans hn)
  exact ⟨s,hs,he ▸ht⟩

theorem UnitFlow.step_left_unique {ss : List Segment} {s t : GridRouting.Point} (hf : UnitFlow ss s t)
    {p q r : GridRouting.Point} (hp : UnitStep ss p r) (hq : UnitStep ss q r) : p=q := by
  obtain ⟨d,hd,hp⟩:=hp
  obtain ⟨e,he,hq⟩:=hq
  have hp':=neighbor_reverse hp
  have hq':=neighbor_reverse hq
  have hde:=hf.incoming_unique r d.opposite e.opposite ⟨p,hp',by simpa using hd⟩ ⟨q,hq',by simpa using he⟩
  rw [hde] at hp'
  exact Option.some.inj (hp'.symm.trans hq')

theorem UnitFlow.step_right_unique {ss : List Segment} {s t : GridRouting.Point} (hf : UnitFlow ss s t)
    {p q r : GridRouting.Point} (hp : UnitStep ss p q) (hq : UnitStep ss p r) : q=r := by
  obtain ⟨d,hd,hp⟩:=hp
  obtain ⟨e,he,hq⟩:=hq
  rw [hf.outgoing_unique p d e hd he] at hp
  exact Option.some.inj (hp.symm.trans hq)

theorem UnitFlow.no_step_source {ss : List Segment} {s t : GridRouting.Point} (hf : UnitFlow ss s t)
    (p : GridRouting.Point) : ¬UnitStep ss p s := by
  rintro ⟨d,hd,hn⟩
  have hi : HasIncoming ss d.opposite s:=⟨p,neighbor_reverse hn,by simpa using hd⟩
  exact ((hf.incoming_iff s).mp ⟨d.opposite,hi⟩).2 rfl

theorem UnitFlow.no_step_target {ss : List Segment} {s t : GridRouting.Point} (hf : UnitFlow ss s t)
    (p : GridRouting.Point) : ¬UnitStep ss t p := by
  rintro ⟨d,hd,_⟩
  exact ((hf.outgoing_iff t).mp ⟨d,hd⟩).2 rfl

end PushPuzzle.PushFS.Reduction

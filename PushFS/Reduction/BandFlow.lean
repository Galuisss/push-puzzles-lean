/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.DirectedRaster
import Mathlib.Data.List.GetD

/-! Exact directed unit flow of the actual six-instruction ordered routing band. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

/-- At least one actual instruction emits this directed unit arc. -/
def HasArc (ss : List Segment) (d : Direction) (p : GridRouting.Point) : Prop := ∃ s∈ss,s.Arc d p

def HasPoint (ss : List Segment) (p : GridRouting.Point) : Prop := ∃ s∈ss,s.Contains p

/-- An incoming direction points from the represented pixel towards its real predecessor. -/
def HasIncoming (ss : List Segment) (d : Direction) (p : GridRouting.Point) : Prop :=
  ∃ q,neighbor d p=some q ∧ HasArc ss d.opposite q

/-- Directed unit-path behavior, including the exact two endpoint exceptions. -/
structure UnitFlow (ss : List Segment) (source target : GridRouting.Point) : Prop where
  source_mem : HasPoint ss source
  target_mem : HasPoint ss target
  outgoing_unique : ∀ p d d',HasArc ss d p → HasArc ss d' p → d=d'
  incoming_unique : ∀ p d d',HasIncoming ss d p → HasIncoming ss d' p → d=d'
  outgoing_iff : ∀ p,(∃ d,HasArc ss d p) ↔ HasPoint ss p ∧ p≠target
  incoming_iff : ∀ p,(∃ d,HasIncoming ss d p) ↔ HasPoint ss p ∧ p≠source
  no_uturn : ∀ p d,HasIncoming ss d p → HasArc ss d p → False

private theorem vertical_contains (x y z : ℕ) (p : GridRouting.Point) :
    (Segment.mk (x,y) (x,z)).Contains p ↔ p.1=x ∧ min y z≤p.2 ∧ p.2≤max y z := by
  dsimp [Segment.Contains]
  omega

private theorem horizontal_contains (x y z : ℕ) (p : GridRouting.Point) :
    (Segment.mk (x,z) (y,z)).Contains p ↔ p.2=z ∧ min x y≤p.1 ∧ p.1≤max x y := by
  dsimp [Segment.Contains]
  omega

namespace Band

def sourceColumn (b : Band) (i : ℕ) : ℕ := b.source.getD i 0
def targetColumn (b : Band) (i : ℕ) : ℕ := b.target.getD i 0
def middleColumn (b : Band) (i : ℕ) : ℕ := (b.source++b.target).sum+i+1
def topBend (b : Band) (i : ℕ) : ℕ := b.source.length-i
def bottomBend (b : Band) (i : ℕ) : ℕ := b.source.length+i+2

private theorem getD_le_sum (xs : List ℕ) (i : ℕ) : xs.getD i 0≤xs.sum := by
  by_cases hi : i<xs.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact List.le_sum_of_mem (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

private theorem source_lt_middle (b : Band) (i : ℕ) : b.sourceColumn i<b.middleColumn i := by
  have hh := getD_le_sum b.source i
  dsimp [sourceColumn,middleColumn]
  rw [List.sum_append]
  omega

private theorem target_lt_middle (b : Band) (i : ℕ) : b.targetColumn i<b.middleColumn i := by
  have hh := getD_le_sum b.target i
  dsimp [targetColumn,middleColumn]
  rw [List.sum_append]
  omega

private theorem bend_order (b : Band) (i : Fin b.source.length) :
    0<b.topBend i.val ∧ b.topBend i.val<b.bottomBend i.val ∧ b.bottomBend i.val<2*(b.source.length+1) := by
  have hi := i.isLt
  dsimp [topBend,bottomBend]
  omega

theorem arc_north (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasArc (Band.curve (b,i.val)) .north p ↔ False := by
  have hi := i.isLt
  simp [HasArc,Band.curve,Segment.Arc]
  omega

theorem arc_east (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasArc (Band.curve (b,i.val)) .east p ↔
      p.2=b.topBend i.val ∧ b.sourceColumn i.val≤p.1 ∧ p.1<b.middleColumn i.val := by
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  simp [HasArc,Band.curve,Segment.Arc,topBend,sourceColumn,targetColumn,middleColumn] at *
  omega

theorem arc_west (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasArc (Band.curve (b,i.val)) .west p ↔
      p.2=b.bottomBend i.val ∧ b.targetColumn i.val<p.1 ∧ p.1≤b.middleColumn i.val := by
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  simp [HasArc,Band.curve,Segment.Arc,bottomBend,sourceColumn,targetColumn,middleColumn] at *
  omega

theorem arc_south (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasArc (Band.curve (b,i.val)) .south p ↔
      (p.1=b.sourceColumn i.val ∧ p.2<b.topBend i.val) ∨
      (p.1=b.middleColumn i.val ∧ b.topBend i.val≤p.2 ∧ p.2<b.bottomBend i.val) ∨
      (p.1=b.targetColumn i.val ∧ b.bottomBend i.val≤p.2 ∧ p.2<2*(b.source.length+1)) := by
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  simp [HasArc,Band.curve,Segment.Arc,topBend,bottomBend,sourceColumn,targetColumn,middleColumn] at *
  omega

/-- Every true point of one actual band wire has at most one outgoing unit direction. -/
private theorem outgoing_unique (b : Band) (i : Fin b.source.length) (p : GridRouting.Point)
    {d d' : Direction} (h : HasArc (Band.curve (b,i.val)) d p)
    (h' : HasArc (Band.curve (b,i.val)) d' p) : d=d' := by
  have ho := b.bend_order i
  cases d <;> cases d'
  all_goals first | rfl | simp only [arc_north,arc_east,arc_west,arc_south] at h h'
  all_goals omega

theorem incoming_north (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasIncoming (Band.curve (b,i.val)) .north p ↔
      (p.1=b.sourceColumn i.val ∧ 0<p.2 ∧ p.2≤b.topBend i.val) ∨
      (p.1=b.middleColumn i.val ∧ b.topBend i.val<p.2 ∧ p.2≤b.bottomBend i.val) ∨
      (p.1=b.targetColumn i.val ∧ b.bottomBend i.val<p.2 ∧ p.2≤2*(b.source.length+1)) := by
  have ho := b.bend_order i
  by_cases hy : p.2=0
  · simp [HasIncoming,neighbor,hy,Direction.opposite]
  · simp [HasIncoming,neighbor,hy,Direction.opposite,arc_south]
    omega

theorem incoming_east (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasIncoming (Band.curve (b,i.val)) .east p ↔
      p.2=b.bottomBend i.val ∧ b.targetColumn i.val≤p.1 ∧ p.1<b.middleColumn i.val := by
  simp [HasIncoming,neighbor,Direction.opposite,arc_west]

theorem incoming_west (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasIncoming (Band.curve (b,i.val)) .west p ↔
      p.2=b.topBend i.val ∧ b.sourceColumn i.val<p.1 ∧ p.1≤b.middleColumn i.val := by
  by_cases hx : p.1=0
  · simp [HasIncoming,neighbor,hx,Direction.opposite]
  · simp [HasIncoming,neighbor,hx,Direction.opposite,arc_east]
    omega

theorem incoming_south (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasIncoming (Band.curve (b,i.val)) .south p ↔ False := by
  simp [HasIncoming,neighbor,Direction.opposite,arc_north]

private theorem incoming_unique (b : Band) (i : Fin b.source.length) (p : GridRouting.Point)
    {d d' : Direction} (h : HasIncoming (Band.curve (b,i.val)) d p)
    (h' : HasIncoming (Band.curve (b,i.val)) d' p) : d=d' := by
  have ho := b.bend_order i
  cases d <;> cases d'
  all_goals first | rfl | simp only [incoming_north,incoming_east,incoming_west,incoming_south] at h h'
  all_goals omega

private theorem no_uturn (b : Band) (i : Fin b.source.length) (p : GridRouting.Point)
    (d : Direction)
    (hi : HasIncoming (Band.curve (b,i.val)) d p) (ho : HasArc (Band.curve (b,i.val)) d p) : False := by
  have hb := b.bend_order i
  cases d <;> simp only [incoming_north,incoming_east,incoming_west,incoming_south,
    arc_north,arc_east,arc_west] at hi ho
  all_goals omega

private theorem trace_iff (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    HasPoint (Band.curve (b,i.val)) p ↔
      (p.1=b.sourceColumn i.val ∧ p.2≤b.topBend i.val) ∨
      (p.2=b.topBend i.val ∧ b.sourceColumn i.val≤p.1 ∧ p.1≤b.middleColumn i.val) ∨
      (p.1=b.middleColumn i.val ∧ b.topBend i.val≤p.2 ∧ p.2≤b.bottomBend i.val) ∨
      (p.2=b.bottomBend i.val ∧ b.targetColumn i.val≤p.1 ∧ p.1≤b.middleColumn i.val) ∨
      (p.1=b.targetColumn i.val ∧ b.bottomBend i.val≤p.2 ∧ p.2≤2*(b.source.length+1)) := by
  have hi := i.isLt
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  simp [HasPoint,Band.curve,vertical_contains,horizontal_contains,topBend,bottomBend,sourceColumn,targetColumn,middleColumn] at *
  omega

private theorem outgoing_iff (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    (∃ d,HasArc (Band.curve (b,i.val)) d p) ↔
      HasPoint (Band.curve (b,i.val)) p ∧ p≠(b.targetColumn i.val,2*(b.source.length+1)) := by
  have hb := b.bend_order i
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  constructor
  · rintro ⟨d,s,hss,ha⟩
    obtain ⟨_,_,hp,_⟩ := ha.endpoints
    refine ⟨⟨s,hss,hp⟩,?_⟩
    intro he
    have h : HasArc (Band.curve (b,i.val)) d p := ⟨s,hss,ha⟩
    subst p
    cases d <;> simp only [arc_north,arc_east,arc_west,arc_south] at h
    all_goals omega
  · rintro ⟨hp,hne⟩
    by_contra hn
    have he : ¬HasArc (Band.curve (b,i.val)) .east p := fun hh => hn ⟨.east,hh⟩
    have hw : ¬HasArc (Band.curve (b,i.val)) .west p := fun hh => hn ⟨.west,hh⟩
    have hso : ¬HasArc (Band.curve (b,i.val)) .south p := fun hh => hn ⟨.south,hh⟩
    have hne' : ¬(p.1=b.targetColumn i.val ∧ p.2=2*(b.source.length+1)) := fun hh => hne (Prod.ext hh.1 hh.2)
    rw [trace_iff] at hp
    simp only [arc_east,arc_west,arc_south] at he hw hso
    omega

private theorem incoming_iff (b : Band) (i : Fin b.source.length) (p : GridRouting.Point) :
    (∃ d,HasIncoming (Band.curve (b,i.val)) d p) ↔
      HasPoint (Band.curve (b,i.val)) p ∧ p≠(b.sourceColumn i.val,0) := by
  have hb := b.bend_order i
  have hs := b.source_lt_middle i.val
  have ht := b.target_lt_middle i.val
  constructor
  · rintro ⟨d,q,hq,s,hss,ha⟩
    obtain ⟨r,hr,_,hp⟩ := ha.endpoints
    have hr' := neighbor_reverse hq
    rw [hr'] at hr
    cases Option.some.inj hr
    refine ⟨⟨s,hss,hp⟩,?_⟩
    intro he
    have h : HasIncoming (Band.curve (b,i.val)) d p := ⟨q,hq,s,hss,ha⟩
    subst p
    cases d <;> simp only [incoming_north,incoming_east,incoming_west,incoming_south] at h
    all_goals omega
  · rintro ⟨hp,hne⟩
    by_contra hn
    have he : ¬HasIncoming (Band.curve (b,i.val)) .east p := fun hh => hn ⟨.east,hh⟩
    have hw : ¬HasIncoming (Band.curve (b,i.val)) .west p := fun hh => hn ⟨.west,hh⟩
    have hno : ¬HasIncoming (Band.curve (b,i.val)) .north p := fun hh => hn ⟨.north,hh⟩
    have hne' : ¬(p.1=b.sourceColumn i.val ∧ p.2=0) := fun hh => hne (Prod.ext hh.1 hh.2)
    rw [trace_iff] at hp
    simp only [incoming_east,incoming_west,incoming_north] at he hw hno
    omega

/-- The whole actual ordered-band route is an ordinary directed wire at every nonendpoint pixel. -/
theorem unitFlow (b : Band) (i : Fin b.source.length) :
    UnitFlow (Band.curve (b,i.val)) (b.sourceColumn i.val,0) (b.targetColumn i.val,2*(b.source.length+1)) where
  source_mem := (trace_iff b i _).mpr (Or.inl ⟨rfl,Nat.zero_le _⟩)
  target_mem := (trace_iff b i _).mpr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl,(bend_order b i).2.2.le,le_rfl⟩))))
  outgoing_unique p _ _ := outgoing_unique b i p
  incoming_unique p _ _ := incoming_unique b i p
  outgoing_iff := outgoing_iff b i
  incoming_iff := incoming_iff b i
  no_uturn := no_uturn b i

end Band
end PushPuzzle.PushFS.Reduction

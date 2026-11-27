/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.ComposeFlow

/-! Literal coordinate translation preserves every unit arc and both endpoint exceptions. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL

theorem hasIncoming_reversed (ss : List Segment) (d : Direction) (p : GridRouting.Point) :
    HasIncoming ss d p ↔ HasArc (ss.map Segment.reversed) d p := by
  constructor
  · rintro ⟨q,hn,s,hs,ha⟩
    exact ⟨s.reversed,List.mem_map.mpr ⟨s,hs,rfl⟩,(s.arc_reverse_step hn).mp ha⟩
  · rintro ⟨r,hr,ha⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    obtain ⟨q,hn,hq⟩ := (s.incoming_reversed d p).mpr ha
    exact ⟨q,hn,s,hs,hq⟩

private theorem Segment.arc_translate (s : Segment) (dx dy : ℕ) (d : Direction)
    (p : GridRouting.Point) :
    (s.translate dx dy).Arc d p ↔ dx≤p.1 ∧ dy≤p.2 ∧ s.Arc d (p.1-dx,p.2-dy) := by
  cases d <;> dsimp [Segment.translate,Segment.Arc] <;> omega

theorem hasArc_translate (ss : List Segment) (dx dy : ℕ) (d : Direction) (p : GridRouting.Point) :
    HasArc (ss.map (fun s=>s.translate dx dy)) d p ↔
      dx≤p.1 ∧ dy≤p.2 ∧ HasArc ss d (p.1-dx,p.2-dy) := by
  constructor
  · rintro ⟨r,hr,ha⟩
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
    obtain ⟨hx,hy,ha⟩ := (s.arc_translate dx dy d p).mp ha
    exact ⟨hx,hy,s,hs,ha⟩
  · rintro ⟨hx,hy,s,hs,ha⟩
    exact ⟨s.translate dx dy,List.mem_map.mpr ⟨s,hs,rfl⟩,(s.arc_translate dx dy d p).mpr ⟨hx,hy,ha⟩⟩

theorem hasPoint_translate (ss : List Segment) (dx dy : ℕ) (p : GridRouting.Point) :
    HasPoint (ss.map (fun s=>s.translate dx dy)) p ↔
      dx≤p.1 ∧ dy≤p.2 ∧ HasPoint ss (p.1-dx,p.2-dy) :=
  Segment.mem_translate_iff ss dx dy p

theorem hasIncoming_translate (ss : List Segment) (dx dy : ℕ) (d : Direction) (p : GridRouting.Point) :
    HasIncoming (ss.map (fun s=>s.translate dx dy)) d p ↔
      dx≤p.1 ∧ dy≤p.2 ∧ HasIncoming ss d (p.1-dx,p.2-dy) := by
  rw [hasIncoming_reversed]
  have hm : (ss.map (fun s=>s.translate dx dy)).map Segment.reversed=
      (ss.map Segment.reversed).map (fun s=>s.translate dx dy) := by
    simp only [List.map_map]
    rfl
  rw [hm,hasArc_translate,← hasIncoming_reversed]

private theorem untranslate_eq (dx dy : ℕ) (p q : GridRouting.Point) (hx : dx≤p.1) (hy : dy≤p.2) :
    (p.1-dx,p.2-dy)=q ↔ p=(q.1+dx,q.2+dy) := by
  simp only [Prod.ext_iff]
  omega

/-- The complete directed path contract is stable under an actual literal translation. -/
theorem UnitFlow.translate {ss : List Segment} {source target : GridRouting.Point}
    (f : UnitFlow ss source target) (dx dy : ℕ) :
    UnitFlow (ss.map (fun s=>s.translate dx dy)) (source.1+dx,source.2+dy) (target.1+dx,target.2+dy) where
  source_mem := by
    apply (hasPoint_translate ss dx dy _).mpr
    refine ⟨by dsimp only; omega,by dsimp only; omega,?_⟩
    simpa only [Nat.add_sub_cancel] using f.source_mem
  target_mem := by
    apply (hasPoint_translate ss dx dy _).mpr
    refine ⟨by dsimp only; omega,by dsimp only; omega,?_⟩
    simpa only [Nat.add_sub_cancel] using f.target_mem
  outgoing_unique p d d' h h' := by
    have ha := (hasArc_translate ss dx dy d p).mp h
    have hb := (hasArc_translate ss dx dy d' p).mp h'
    exact f.outgoing_unique _ d d' ha.2.2 hb.2.2
  incoming_unique p d d' h h' := by
    have ha := (hasIncoming_translate ss dx dy d p).mp h
    have hb := (hasIncoming_translate ss dx dy d' p).mp h'
    exact f.incoming_unique _ d d' ha.2.2 hb.2.2
  outgoing_iff p := by
    constructor
    · rintro ⟨d,ha⟩
      obtain ⟨hx,hy,ha⟩ := (hasArc_translate ss dx dy d p).mp ha
      obtain ⟨hp,hne⟩ := (f.outgoing_iff _).mp ⟨d,ha⟩
      exact ⟨(hasPoint_translate ss dx dy p).mpr ⟨hx,hy,hp⟩,
        fun he => hne ((untranslate_eq dx dy p target hx hy).mpr he)⟩
    · rintro ⟨hp,hne⟩
      obtain ⟨hx,hy,hp⟩ := (hasPoint_translate ss dx dy p).mp hp
      have hn : (p.1-dx,p.2-dy)≠target := fun he => hne ((untranslate_eq dx dy p target hx hy).mp he)
      obtain ⟨d,ha⟩ := (f.outgoing_iff _).mpr ⟨hp,hn⟩
      exact ⟨d,(hasArc_translate ss dx dy d p).mpr ⟨hx,hy,ha⟩⟩
  incoming_iff p := by
    constructor
    · rintro ⟨d,ha⟩
      obtain ⟨hx,hy,ha⟩ := (hasIncoming_translate ss dx dy d p).mp ha
      obtain ⟨hp,hne⟩ := (f.incoming_iff _).mp ⟨d,ha⟩
      exact ⟨(hasPoint_translate ss dx dy p).mpr ⟨hx,hy,hp⟩,
        fun he => hne ((untranslate_eq dx dy p source hx hy).mpr he)⟩
    · rintro ⟨hp,hne⟩
      obtain ⟨hx,hy,hp⟩ := (hasPoint_translate ss dx dy p).mp hp
      have hn : (p.1-dx,p.2-dy)≠source := fun he => hne ((untranslate_eq dx dy p source hx hy).mp he)
      obtain ⟨d,ha⟩ := (f.incoming_iff _).mpr ⟨hp,hn⟩
      exact ⟨d,(hasIncoming_translate ss dx dy d p).mpr ⟨hx,hy,ha⟩⟩
  no_uturn p d hi ho :=
    f.no_uturn _ d ((hasIncoming_translate ss dx dy d p).mp hi).2.2 ((hasArc_translate ss dx dy d p).mp ho).2.2

end PushPuzzle.PushFS.Reduction

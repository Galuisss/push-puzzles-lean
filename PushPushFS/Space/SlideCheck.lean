/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushFS.Basic
public import PushPush.Space.SlideCheck

/-! Polynomial-time maximum-slide checks with immutable walls. -/

@[expose] public section
namespace PushPuzzle.PushPushFS.Machine

open PushFS (Cell Direction Adjacent State Instance)
open PushFS.Machine PushPush.Machine
open Turing.MultiTapeTM ComputableInPolyTime

/-- Check every floor cell, the full moving run, and its first stopping obstacle. -/
def checkSlide (I : Instance) (d : Direction) (u : List Bool) (p : RawCell) (n k : ℕ) : Bool :=
  ((List.range (n + k + 1)).all fun i =>
    decide ((advance d p i).1 < I.width) && decide ((advance d p i).2 < I.height) &&
      !wallAt (I, advance d p i)) &&
  ((List.range (n + k)).all fun i => adjacent (d, advance d p i, advance d p (i + 1))) &&
  ((List.range n).all fun i => boxAt (I, u, advance d p (i + 1))) &&
  ((List.range k).all fun i => !boxAt (I, u, advance d p (n + i + 1))) &&
  ((cells (I.width, I.height)).all fun q =>
    !adjacent (d, advance d p (n + k), q) || boxAt (I, u, q) || wallAt (I, q))

@[fun_prop] theorem checkSlide_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × RawCell × ℕ × ℕ =>
        checkSlide q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction)
        (encPair encBits (encPair encRawCell (encPair encUnary encUnary))))) encBool := by
  unfold checkSlide
  fun_prop

private def rayCell (I : Instance) (d : Direction) (p : RawCell) (length : ℕ)
    (hf : ∀ i, i < length →
      ((advance d p i).1 < I.width ∧ (advance d p i).2 < I.height) ∧
        wallAt (I, advance d p i) = false) : Fin length → Cell I.width I.height :=
  fun i => (⟨(advance d p i).1, (hf i i.isLt).1.1⟩,
    ⟨(advance d p i).2, (hf i i.isLt).1.2⟩)

private theorem rayCell_floor (I : Instance) (d : Direction) (p : RawCell) (length : ℕ)
    (hf : ∀ i, i < length →
      ((advance d p i).1 < I.width ∧ (advance d p i).2 < I.height) ∧
        wallAt (I, advance d p i) = false) (i : Fin length) :
    rayCell I d p length hf i ∉ I.board.walls := by
  have hi := (hf i i.isLt).2
  change wallAt (I, rawCell (rayCell I d p length hf i)) = false at hi
  rw [wallAt_correct] at hi
  exact of_decide_eq_false hi

private theorem slide_of_check (I : Instance) (d : Direction) (s : State I.width I.height)
    (n k : ℕ) (hc : checkSlide I d s.bits (rawCell s.player) n k = true) :
    Nonempty (Slide I.board d s n k) := by
  simp only [checkSlide, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', forall_cells_iff] at hc
  obtain ⟨⟨⟨⟨hf, ha⟩, hb⟩, he⟩, hstop⟩ := hc
  let cell := rayCell I d (rawCell s.player) (n + k + 1) hf
  have hcell (i : Fin (n + k + 1)) :
      rawCell (cell i) = advance d (rawCell s.player) i := rfl
  have hfloor := rayCell_floor I d (rawCell s.player) (n + k + 1) hf
  refine ⟨⟨⟨cell, ?_, ?_, ?_, ?_, ?_⟩, hfloor⟩⟩
  · apply rawCell_injective
    cases d <;> simp [hcell, advance, blocked]
  · intro i
    apply (adjacent_correct d _ _).mp
    simpa only [hcell, Fin.val_castSucc, Fin.val_succ] using ha i i.isLt
  · intro i
    have hi := hb i i.isLt
    rw [← hcell ⟨i.val + 1, by omega⟩, boxAt_correct] at hi
    exact Finset.mem_union_left _ (of_decide_eq_true hi)
  · intro i
    have hi := he i i.isLt
    rw [← hcell ⟨n + i.val + 1, by omega⟩, boxAt_correct] at hi
    intro hp
    exact (Finset.mem_union.mp hp).elim (of_decide_eq_false hi) (hfloor _)
  · intro q hq
    have hs := hstop q
    rw [← hcell ⟨n + k, by omega⟩, Bool.or_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', boxAt_correct, wallAt_correct] at hs
    rcases hs with (hs | hs) | hs
    · have ht := (adjacent_correct d _ _).mpr hq
      rw [ht] at hs
      contradiction
    · exact Finset.mem_union_left _ (of_decide_eq_true hs)
    · exact Finset.mem_union_right _ (of_decide_eq_true hs)

private theorem check_of_slide (I : Instance) (d : Direction) (s : State I.width I.height)
    {n k : ℕ} (r : Slide I.board d s n k) :
    checkSlide I d s.bits (rawCell s.player) n k = true := by
  simp only [checkSlide, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', forall_cells_iff]
  have hc := advance_slide r.ray
  simp only [blocked] at hc
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · intro i hi
    rw [← hc ⟨i, hi⟩]
    exact ⟨⟨(r.cell ⟨i, hi⟩).1.isLt, (r.cell ⟨i, hi⟩).2.isLt⟩,
      by rw [wallAt_correct]; exact decide_eq_false (r.floor _)⟩
  · intro i hi
    rw [← hc ⟨i, by omega⟩, ← hc ⟨i + 1, by omega⟩, adjacent_correct]
    exact r.ray.adjacent ⟨i, hi⟩
  · intro i hi
    rw [← hc ⟨i + 1, by omega⟩, boxAt_correct]
    exact decide_eq_true (r.occupied ⟨i, hi⟩)
  · intro i hi
    rw [← hc ⟨n + i + 1, by omega⟩, boxAt_correct]
    exact decide_eq_false (fun hp => r.ray.clear ⟨i, hi⟩ (Finset.mem_union_left _ hp))
  · intro q
    rw [← hc ⟨n + k, by omega⟩, Bool.or_eq_true, Bool.or_eq_true,
      Bool.not_eq_true', boxAt_correct, wallAt_correct]
    by_cases hq : Adjacent d (r.cell ⟨n + k, by omega⟩) q
    · rcases Finset.mem_union.mp (r.ray.stopped q hq) with hb | hw
      · exact Or.inl (Or.inr (decide_eq_true hb))
      · exact Or.inr (decide_eq_true hw)
    · apply Or.inl ∘ Or.inl
      have hf : adjacent (d, rawCell (r.cell ⟨n + k, by omega⟩), rawCell q) ≠ true :=
        fun he => hq ((adjacent_correct d _ _).mp he)
      cases hv : adjacent (d, rawCell (r.cell ⟨n + k, by omega⟩), rawCell q) <;>
        simp_all

theorem checkSlide_correct (I : Instance) (d : Direction) (s : State I.width I.height)
    (n k : ℕ) :
    checkSlide I d s.bits (rawCell s.player) n k = true ↔
      Nonempty (Slide I.board d s n k) :=
  ⟨slide_of_check I d s n k, fun ⟨r⟩ => check_of_slide I d s r⟩

theorem checkUpdate_correct (I : Instance) (d : Direction)
    (s t : State I.width I.height) {n k : ℕ} (r : Slide I.board d s n k) :
    PushPush.Machine.checkUpdate I d s.bits t.bits (rawCell s.player) n k = true ↔ t.boxes = r.boxes := by
  simp only [PushPush.Machine.checkUpdate, List.all_eq_true,
    forall_cells_iff, beq_iff_eq]
  have hbefore (q : Cell I.width I.height) :
      onRay d (rawCell s.player) 1 n (rawCell q) = decide (q ∈ r.before) :=
    by
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact onRay_before r.ray q
  have hafter (q : Cell I.width I.height) :
      onRay d (rawCell s.player) (k + 1) n (rawCell q) = decide (q ∈ r.after) :=
    by
      apply Bool.eq_iff_iff.mpr
      rw [decide_eq_true_eq]
      exact onRay_after r.ray q
  simp only [boxAt_correct, hbefore, hafter, ← decide_not, ← Bool.decide_and,
    ← Bool.decide_or, decide_eq_decide, Slide.boxes]
  constructor
  · intro h
    ext q
    simpa only [Finset.mem_union, Finset.mem_sdiff] using h q
  · intro h q
    simpa only [Finset.mem_union, Finset.mem_sdiff] using Finset.ext_iff.mp h q

end PushPuzzle.PushPushFS.Machine

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Slide
public import PushFS.Space.RunCheck
public import PushFS.Space.StateDecoding

/-! A direct polynomial-time maximum-slide checker on dense state words. -/

@[expose] public section
namespace PushPuzzle.PushPush.Machine

open PushFS (Cell Direction Adjacent State Instance)
open PushFS.Machine
open Turing.MultiTapeTM ComputableInPolyTime

theorem rawCell_injective {w h : ℕ} : Function.Injective (rawCell (w := w) (h := h)) := by
  intro p q he
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

theorem advance_slide {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (i : Fin (n + k + 1)) :
    rawCell (r.cell i) = advance d (rawCell s.player) i.val := by
  have hp := r.position i
  have hl := r.lane i
  cases d <;> simp only [Direction.position, Direction.lane, advance, rawCell] at * <;>
    apply Prod.ext <;> omega

theorem slide_length_le {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) : n + k + 1 ≤ w * h := by
  have hc := Fintype.card_le_of_injective r.cell r.injective
  simpa only [Fintype.card_fin, Fintype.card_prod] using hc

/-- Ray bounds, adjacency, its occupied prefix and clear suffix, and the final stop. -/
def checkSlide (I : Instance) (d : Direction) (u : List Bool) (p : RawCell) (n k : ℕ) : Bool :=
  ((List.range (n + k + 1)).all fun i =>
    decide ((advance d p i).1 < I.width) && decide ((advance d p i).2 < I.height)) &&
  ((List.range (n + k)).all fun i => adjacent (d, advance d p i, advance d p (i + 1))) &&
  ((List.range n).all fun i => boxAt (I, u, advance d p (i + 1))) &&
  ((List.range k).all fun i => !boxAt (I, u, advance d p (n + i + 1))) &&
  ((cells (I.width, I.height)).all fun q =>
    !adjacent (d, advance d p (n + k), q) || boxAt (I, u, q))

@[fun_prop] theorem checkSlide_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × RawCell × ℕ × ℕ =>
        checkSlide q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction)
        (encPair encBits (encPair encRawCell (encPair encUnary encUnary))))) encBool := by
  unfold checkSlide
  fun_prop

theorem checkSlide_correct (I : Instance) (d : Direction) (s : State I.width I.height)
    (n k : ℕ) :
    checkSlide I d s.bits (rawCell s.player) n k = true ↔ Nonempty (Slide d s n k) := by
  simp only [checkSlide, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true', forall_cells_iff]
  constructor
  · rintro ⟨⟨⟨⟨hf, ha⟩, hb⟩, he⟩, hstop⟩
    let cell : Fin (n + k + 1) → Cell I.width I.height := fun i =>
      (⟨(advance d (rawCell s.player) i).1, (hf i i.isLt).1⟩,
       ⟨(advance d (rawCell s.player) i).2, (hf i i.isLt).2⟩)
    have hcell (i : Fin (n + k + 1)) :
        rawCell (cell i) = advance d (rawCell s.player) i := rfl
    refine ⟨⟨cell, ?_, ?_, ?_, ?_, ?_⟩⟩
    · apply rawCell_injective
      cases d <;> simp [hcell, advance]
    · intro i
      apply (adjacent_correct d _ _).mp
      simpa only [hcell, Fin.val_castSucc, Fin.val_succ] using ha i i.isLt
    · intro i
      have hi := hb i i.isLt
      rw [← hcell ⟨i.val + 1, by omega⟩, boxAt_correct] at hi
      exact of_decide_eq_true hi
    · intro i
      have hi := he i i.isLt
      rw [← hcell ⟨n + i.val + 1, by omega⟩, boxAt_correct] at hi
      exact of_decide_eq_false hi
    · intro q hq
      have hs := hstop q
      rw [← hcell ⟨n + k, by omega⟩, Bool.or_eq_true, Bool.not_eq_true',
        boxAt_correct] at hs
      rcases hs with hs | hs
      · have ht := (adjacent_correct d _ _).mpr hq
        rw [ht] at hs
        contradiction
      · exact of_decide_eq_true hs
  · rintro ⟨r⟩
    have hc := advance_slide r
    refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩
    · intro i hi
      rw [← hc ⟨i, hi⟩]
      exact ⟨(r.cell ⟨i, hi⟩).1.isLt, (r.cell ⟨i, hi⟩).2.isLt⟩
    · intro i hi
      rw [← hc ⟨i, by omega⟩, ← hc ⟨i + 1, by omega⟩, adjacent_correct]
      exact r.adjacent ⟨i, hi⟩
    · intro i hi
      rw [← hc ⟨i + 1, by omega⟩, boxAt_correct]
      exact decide_eq_true (r.occupied ⟨i, hi⟩)
    · intro i hi
      rw [← hc ⟨n + i + 1, by omega⟩, boxAt_correct]
      exact decide_eq_false (r.clear ⟨i, hi⟩)
    · intro q
      rw [← hc ⟨n + k, by omega⟩, Bool.or_eq_true, Bool.not_eq_true', boxAt_correct]
      by_cases hq : Adjacent d (r.cell ⟨n + k, by omega⟩) q
      · exact Or.inr (decide_eq_true (r.stopped q hq))
      · apply Or.inl
        have hf : adjacent (d, rawCell (r.cell ⟨n + k, by omega⟩), rawCell q) ≠ true :=
          fun he => hq ((adjacent_correct d _ _).mp he)
        cases hv : adjacent (d, rawCell (r.cell ⟨n + k, by omega⟩), rawCell q) <;>
          simp_all

/-- Membership in a finite directional ray interval. -/
def onRay (d : Direction) (p : RawCell) (first n : ℕ) (q : RawCell) : Bool :=
  (List.range n).any fun i => advance d p (first + i) == q

@[fun_prop] theorem onRay_polyTime :
    ComputableInPolyTime
      (fun q : Direction × RawCell × ℕ × ℕ × RawCell =>
        onRay q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (encPair (encFinite Direction)
        (encPair encRawCell (encPair encUnary (encPair encUnary encRawCell)))) encBool := by
  unfold onRay
  fun_prop

theorem onRay_before {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (q : Cell w h) :
    onRay d (rawCell s.player) 1 n (rawCell q) = true ↔ q ∈ r.before := by
  simp only [onRay, List.any_eq_true, List.mem_range, beq_iff_eq, Slide.before,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨⟨i, hi⟩, rawCell_injective ?_⟩
    rw [advance_slide]
    simpa only [Nat.add_comm 1] using he
  · rintro ⟨i, rfl⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [advance_slide]
    change advance d (rawCell s.player) (1 + i.val) =
      advance d (rawCell s.player) (i.val + 1)
    rw [Nat.add_comm]

theorem onRay_after {w h n k : ℕ} {d : Direction} {s : State w h}
    (r : Slide d s n k) (q : Cell w h) :
    onRay d (rawCell s.player) (k + 1) n (rawCell q) = true ↔ q ∈ r.after := by
  simp only [onRay, List.any_eq_true, List.mem_range, beq_iff_eq, Slide.after,
    Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, he⟩
    refine ⟨⟨i, hi⟩, rawCell_injective ?_⟩
    rw [advance_slide]
    simpa only [Nat.add_right_comm k 1] using he
  · rintro ⟨i, rfl⟩
    refine ⟨i, i.isLt, ?_⟩
    rw [advance_slide]
    change advance d (rawCell s.player) (k + 1 + i.val) =
      advance d (rawCell s.player) (k + i.val + 1)
    rw [Nat.add_right_comm k 1]

/-- Compare all target bits with the translated complete box run. -/
def checkUpdate (I : Instance) (d : Direction) (u v : List Bool)
    (p : RawCell) (n k : ℕ) : Bool :=
  (cells (I.width, I.height)).all fun q =>
    boxAt (I, v, q) ==
      ((boxAt (I, u, q) && !onRay d p 1 n q) || onRay d p (k + 1) n q)

@[fun_prop] theorem checkUpdate_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × List Bool × RawCell × ℕ × ℕ =>
        checkUpdate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2)
      (encPair PushFS.encoding (encPair (encFinite Direction)
        (encPair encBits (encPair encBits (encPair encRawCell
          (encPair encUnary encUnary)))))) encBool := by
  unfold checkUpdate
  fun_prop

theorem checkUpdate_correct (I : Instance) (d : Direction)
    (s t : State I.width I.height) {n k : ℕ} (r : Slide d s n k) :
    checkUpdate I d s.bits t.bits (rawCell s.player) n k = true ↔ t.boxes = r.boxes := by
  simp only [checkUpdate, List.all_eq_true, forall_cells_iff, beq_iff_eq]
  have hbefore (q : Cell I.width I.height) :
      onRay d (rawCell s.player) 1 n (rawCell q) = decide (q ∈ r.before) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using onRay_before r q)
  have hafter (q : Cell I.width I.height) :
      onRay d (rawCell s.player) (k + 1) n (rawCell q) = decide (q ∈ r.after) :=
    Bool.eq_iff_iff.mpr (by simpa only [decide_eq_true_eq] using onRay_after r q)
  simp only [boxAt_correct, hbefore, hafter, ← decide_not, ← Bool.decide_and,
    ← Bool.decide_or, decide_eq_decide,
    Slide.boxes]
  constructor
  · intro h
    ext q
    simpa only [Finset.mem_union, Finset.mem_sdiff] using h q
  · intro h q
    simpa only [Finset.mem_union, Finset.mem_sdiff] using Finset.ext_iff.mp h q

end PushPuzzle.PushPush.Machine

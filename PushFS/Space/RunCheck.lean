/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.Queries

/-! A uniform polynomial-time checker for consecutive box runs. -/

@[expose] public section

namespace PushPuzzle.PushFS.Machine


open Turing.MultiTapeTM ComputableInPolyTime

/-- A raw coordinate at a unary distance in one direction. -/
def advance (d : Direction) (p : RawCell) (n : ℕ) : RawCell :=
  match d with
  | .north => (p.1, p.2 - n)
  | .east => (p.1 + n, p.2)
  | .south => (p.1, p.2 + n)
  | .west => (p.1 - n, p.2)

@[fun_prop] theorem advance_polyTime :
    ComputableInPolyTime (fun q : Direction × RawCell × ℕ => advance q.1 q.2.1 q.2.2)
      (encPair (encFinite Direction) (encPair encRawCell encUnary)) encRawCell := by
  apply finite_cases (tag := fun q : Direction × RawCell × ℕ => q.1)
    (branch := fun d q => advance d q.2.1 q.2.2) (by fun_prop)
  intro d
  cases d <;> simp only [advance] <;> fun_prop

theorem advance_run {w h n : ℕ} {B : Board w h} {d : Direction} {s : State w h}
    (r : Run B d s n) (i : Fin (n + 2)) :
    rawCell (r.cell i) = advance d (rawCell s.player) i.val := by
  have hp := r.position i
  have hl := r.lane i
  cases d <;> simp only [Direction.position, Direction.lane, advance, rawCell] at * <;>
    apply Prod.ext <;> omega

private theorem rawCell_injective {w h : ℕ} : Function.Injective (rawCell (w := w) (h := h)) := by
  intro p q he
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst he
  · exact congrArg Prod.snd he

/-- Bounds, floor, consecutive adjacency, occupied interior and empty endpoint. -/
def checkRun (I : Instance) (d : Direction) (u : List Bool) (p : RawCell) (n : ℕ) : Bool :=
  ((List.range (n + 2)).all fun i =>
    decide ((advance d p i).1 < I.width) && decide ((advance d p i).2 < I.height) &&
      !wallAt (I, advance d p i)) &&
  ((List.range (n + 1)).all fun i => adjacent (d, advance d p i, advance d p (i + 1))) &&
  ((List.range n).all fun i => boxAt (I, u, advance d p (i + 1))) &&
  !boxAt (I, u, advance d p (n + 1))

@[fun_prop] theorem checkRun_polyTime :
    ComputableInPolyTime
      (fun q : Instance × Direction × List Bool × RawCell × ℕ =>
        checkRun q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
      (encPair encoding (encPair (encFinite Direction)
        (encPair encBits (encPair encRawCell encUnary)))) encBool := by
  unfold checkRun
  fun_prop

/-- The raw checker accepts exactly the runs in the operational semantics. -/
theorem checkRun_correct (I : Instance) (d : Direction) (s : State I.width I.height) (n : ℕ) :
    checkRun I d s.bits (rawCell s.player) n = true ↔ Nonempty (Run I.board d s n) := by
  simp only [checkRun, Bool.and_eq_true, List.all_eq_true, List.mem_range,
    decide_eq_true_eq, Bool.not_eq_true']
  constructor
  · rintro ⟨⟨⟨hf, ha⟩, hb⟩, he⟩
    let cell : Fin (n + 2) → Cell I.width I.height := fun i =>
      (⟨(advance d (rawCell s.player) i).1, (hf i i.isLt).1.1⟩,
       ⟨(advance d (rawCell s.player) i).2, (hf i i.isLt).1.2⟩)
    have hcell (i : Fin (n + 2)) : rawCell (cell i) = advance d (rawCell s.player) i := rfl
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
    · have hi := he
      rw [← hcell ⟨n + 1, by omega⟩, boxAt_correct] at hi
      exact of_decide_eq_false hi
    · intro i
      have hi := (hf i i.isLt).2
      rw [← hcell i, wallAt_correct] at hi
      exact of_decide_eq_false hi
  · rintro ⟨r⟩
    have hc := advance_run r
    refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
    · intro i hi
      rw [← hc ⟨i, hi⟩]
      refine ⟨⟨(r.cell ⟨i, hi⟩).1.isLt, (r.cell ⟨i, hi⟩).2.isLt⟩, ?_⟩
      rw [wallAt_correct]
      exact decide_eq_false (r.floor _)
    · intro i hi
      rw [← hc ⟨i, by omega⟩, ← hc ⟨i + 1, by omega⟩, adjacent_correct]
      exact r.adjacent ⟨i, hi⟩
    · intro i hi
      rw [← hc ⟨i + 1, by omega⟩, boxAt_correct]
      exact decide_eq_true (r.occupied ⟨i, hi⟩)
    · rw [← hc ⟨n + 1, by omega⟩, boxAt_correct]
      exact decide_eq_false r.empty

end PushPuzzle.PushFS.Machine

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PermutationWalkWord

/-! Actual chains of nonempty blocks joined by their original indexed bridge occurrences. -/

public section
namespace PushPuzzle.List


open _root_.List

/-- Read every literal block in order, inserting precisely its original intervening bridge. -/
@[expose] def blockWalk {α : Type*} {n : ℕ} (blocks : Fin (n + 1) → List α) (bridges : Fin n → α) : List α :=
  (alternatingWalk blocks (fun index => [bridges index])).flatten

/-- The first actual block and bridge precede exactly the shifted remaining blocks. -/
theorem blockWalk_succ {α : Type*} {n : ℕ} (blocks : Fin (n + 2) → List α) (bridges : Fin (n + 1) → α) :
    blockWalk blocks bridges = blocks 0 ++ bridges 0 :: blockWalk (fun index => blocks index.succ) (fun index => bridges index.succ) := by
  rw [blockWalk, alternatingWalk_succ]
  rfl

/-- Complete local chains and their actual two joining steps form the same complete block chain. -/
theorem blockWalk_isChainFromTo {α : Type*} {r : α → α → Prop} {n : ℕ}
    (blocks : Fin (n + 1) → List α) (bridges : Fin n → α) (starts finishes : Fin (n + 1) → α)
    (hblock : ∀ index, (blocks index).IsChainFromTo r (starts index) (finishes index))
    (hleft : ∀ index, r (finishes index.castSucc) (bridges index))
    (hright : ∀ index, r (bridges index) (starts index.succ)) :
    (blockWalk blocks bridges).IsChainFromTo r (starts 0) (finishes (Fin.last n)) := by
  induction n with
  | zero => simpa only [blockWalk, alternatingWalk, List.ofFn_zero, List.flatten_nil, List.flatten_cons, List.append_nil, Fin.last_zero] using hblock 0
  | succ n ih =>
    rw [blockWalk_succ]
    have htail := ih (fun index => blocks index.succ) (fun index => bridges index.succ)
      (fun index => starts index.succ) (fun index => finishes index.succ) (fun index => hblock index.succ)
      (fun index => by simpa only [Fin.succ_castSucc] using hleft index.succ) (fun index => hright index.succ)
    have hwhole := (PushPuzzle.List.IsChainFromTo.append_step ((hblock 0).snoc (hleft 0))) htail (hright 0)
    simpa only [append_assoc, singleton_append, Fin.succ_last] using hwhole

/-- The block walk preserves exactly every block occurrence and original bridge. -/
theorem mem_blockWalk_iff {α : Type*} {n : ℕ} (blocks : Fin (n + 1) → List α) (bridges : Fin n → α) (x : α) :
    x ∈ blockWalk blocks bridges ↔ (∃ index, x ∈ blocks index) ∨ (∃ index, bridges index = x) := by
  simp only [blockWalk, mem_flatten, mem_alternatingWalk_iff]
  constructor
  · rintro ⟨word, (⟨index, rfl⟩ | ⟨index, rfl⟩), hx⟩
    · exact Or.inl ⟨index, hx⟩
    · exact Or.inr ⟨index, (List.mem_singleton.mp hx).symm⟩
  · rintro (⟨index, hx⟩ | ⟨index, rfl⟩)
    · exact ⟨blocks index, Or.inl ⟨index, rfl⟩, hx⟩
    · exact ⟨[bridges index], Or.inr ⟨index, rfl⟩, by simp⟩

/-- The block word's exact length counts the original local words and one occurrence per bridge. -/
theorem blockWalk_length {α : Type*} {n : ℕ} (blocks : Fin (n + 1) → List α) (bridges : Fin n → α) :
    (blockWalk blocks bridges).length = (List.ofFn (fun index => (blocks index).length)).sum + n := by
  induction n with
  | zero => simp [blockWalk, alternatingWalk]
  | succ n ih =>
    rw [blockWalk_succ, length_append, length_cons, ih]
    conv_rhs => rw [List.ofFn_succ, List.sum_cons]
    omega

end PushPuzzle.List

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import Cslib.Foundations.Data.List.IsChainFromTo
public import Mathlib.GroupTheory.Perm.List
public import Mathlib.Data.Fintype.Card

/-! Literal alternating walks and closed complete permutation words. -/

public section
namespace PushPuzzle.List


open _root_.List

/-- A complete finite word using at most one occurrence per available element is duplicate-free. -/
theorem nodup_of_complete_length_le_card {α : Type*} [Fintype α] [DecidableEq α] (word : List α)
    (hcover : ∀ x : α, x ∈ word) (hlen : word.length ≤ Fintype.card α) : word.Nodup := by
  have hall : word.toFinset = Finset.univ := Finset.eq_univ_of_forall (fun x => List.mem_toFinset.mpr (hcover x))
  apply List.nodup_iff_le_length_dedup.mpr
  rw [← List.card_toFinset, hall, Finset.card_univ]
  exact hlen

/-- Alternately read successive path ends and the intervening original contour occurrences. -/
@[expose] def alternatingWalk {α : Type*} {n : ℕ} (ends : Fin (n + 1) → α) (between : Fin n → α) : List α :=
  ends 0 :: (List.ofFn (fun index => [between index, ends index.succ])).flatten

/-- Peeling the actual first path step retains all the original shifted finite indices. -/
theorem alternatingWalk_succ {α : Type*} {n : ℕ} (ends : Fin (n + 2) → α) (between : Fin (n + 1) → α) :
    alternatingWalk ends between = ends 0 :: between 0 :: alternatingWalk (fun index => ends index.succ) (fun index => between index.succ) := by
  unfold alternatingWalk
  rw [List.ofFn_succ]
  rfl

/-- Every original path end and intermediate occurrence remains in the literal alternating word. -/
theorem mem_alternatingWalk_iff {α : Type*} {n : ℕ} (ends : Fin (n + 1) → α) (between : Fin n → α) (x : α) :
    x ∈ alternatingWalk ends between ↔ (∃ index, ends index = x) ∨ (∃ index, between index = x) := by
  simp only [alternatingWalk, mem_cons, mem_flatten, mem_ofFn]
  constructor
  · rintro (rfl | ⟨_, ⟨index, rfl⟩, hm⟩)
    · exact Or.inl ⟨0, rfl⟩
    · simp only [mem_cons, not_mem_nil, or_false] at hm
      rcases hm with he | he
      · exact Or.inr ⟨index, he.symm⟩
      · exact Or.inl ⟨index.succ, he.symm⟩
  · rintro (⟨index, rfl⟩ | ⟨index, rfl⟩)
    · refine Fin.cases (Or.inl rfl) (fun index => ?_) index
      exact Or.inr ⟨_, ⟨index, rfl⟩, by simp⟩
    · exact Or.inr ⟨_, ⟨index, rfl⟩, by simp⟩

/-- The alternating word counts every original path end and one occurrence per gap. -/
theorem alternatingWalk_length {α : Type*} {n : ℕ} (ends : Fin (n + 1) → α) (between : Fin n → α) :
    (alternatingWalk ends between).length = 2 * n + 1 := by
  simp [alternatingWalk, length_flatten, map_ofFn, Function.comp_def, List.ofFn_const, Nat.mul_comm]

/-- The literal alternating array is the complete designated endpoint chain. -/
theorem alternatingWalk_isChainFromTo {α : Type*} {r : α → α → Prop} {n : ℕ}
    (ends : Fin (n + 1) → α) (between : Fin n → α)
    (hfirst : ∀ index, r (ends index.castSucc) (between index))
    (hsecond : ∀ index, r (between index) (ends index.succ)) :
    (alternatingWalk ends between).IsChainFromTo r (ends 0) (ends (Fin.last n)) := by
  induction n with
  | zero => exact isChainFromTo_singleton
  | succ n ih =>
    rw [alternatingWalk_succ]
    exact ((ih (fun index => ends index.succ) (fun index => between index.succ)
      (fun index => by simpa only [Fin.succ_castSucc] using hfirst index.succ) (fun index => hsecond index.succ)).cons
        (hsecond 0)).cons (hfirst 0)

/-- Concatenate two designated chains through their actual joining step. -/
theorem IsChainFromTo.append_step {α : Type*} {r : α → α → Prop} {left right : List α} {a b c d : α}
    (hl : left.IsChainFromTo r a b) (hr : right.IsChainFromTo r c d) (hstep : r b c) :
    (left ++ right).IsChainFromTo r a d := by
  have hc := (hl.snoc hstep).append_tail hr
  have he : c :: right.tail = right := by rw [← hr.head_eq]; exact right.cons_head_tail hr.ne_nil
  simpa only [append_assoc, singleton_append, he] using hc

/-- Reversing the literal chain exchanges its designated endpoints and reverses its relation. -/
theorem IsChainFromTo.reverse_chain {α : Type*} {r : α → α → Prop} {word : List α} {a b : α}
    (h : word.IsChainFromTo r a b) : word.reverse.IsChainFromTo (fun x y => r y x) b a := by
  refine ⟨List.isChain_reverse.mpr h.isChain, (List.reverse_ne_nil_iff.mpr h.ne_nil), ?_, ?_⟩
  · simpa only [List.head_reverse] using h.getLast_eq
  · simpa only [List.getLast_reverse] using h.head_eq

/-- A complete closed chain with distinct occurrences gives exactly its actual permutation. -/
theorem IsChainFromTo.perm_eq_formPerm {α : Type*} [DecidableEq α] {word : List α} {a b : α}
    (perm : Equiv.Perm α) (hchain : word.IsChainFromTo (fun x y => perm x = y) a b)
    (hclose : perm b = a) (hn : word.Nodup) (hcover : ∀ x : α, x ∈ word) : perm = word.formPerm := by
  apply Equiv.ext
  intro x
  obtain ⟨index, hi, rfl⟩ := List.getElem_of_mem (hcover x)
  rw [formPerm_apply_getElem word hn index hi]
  by_cases hnext : index + 1 < word.length
  · simpa only [Nat.mod_eq_of_lt hnext] using hchain.isChain.getElem index hnext
  · have he : index = word.length - 1 := by omega
    have hlen : index + 1 = word.length := by omega
    have hmod : (index + 1) % word.length = 0 := by rw [hlen, Nat.mod_self]
    have hget : word[index] = b := by simpa only [he] using hchain.getElem_length_sub_one
    simpa only [hmod, hget, hchain.getElem_zero] using hclose

end PushPuzzle.List

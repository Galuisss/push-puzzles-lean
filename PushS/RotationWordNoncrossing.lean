/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.Graph.RotationSystem.IntersectionParity
public import Mathlib.GroupTheory.Perm.List
import Lean.Elab.Tactic.Omega

/-! Literal rotation intervals and alternation in a complete directed cyclic word. -/

public section
namespace PushPuzzle.Graph.RotationSystem

open Cslib.Complexity.Graph.RotationSystem

open Cslib.Complexity.Graph

open Cslib.Complexity

private def wordDistance (length first last : ℕ) : ℕ :=
  if first ≤ last then last - first else length - first + last

private theorem wordDistance_spec {length first last : ℕ}
    (hf : first < length) (hl : last < length) :
    wordDistance length first last < length ∧
      (first + wordDistance length first last) % length = last ∧
      ∀ k < wordDistance length first last, (first + k) % length ≠ last := by
  unfold wordDistance
  split_ifs with h
  · refine ⟨by omega, ?_, ?_⟩
    · rw [show first + (last - first) = last by omega, Nat.mod_eq_of_lt hl]
    · intro k hk
      rw [Nat.mod_eq_of_lt (show first + k < length by omega)]
      omega
  · refine ⟨by omega, ?_, ?_⟩
    · rw [show first + (length - first + last) = length + last by omega,
        Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hl]
    · intro k hk he
      by_cases hs : first + k < length
      · rw [Nat.mod_eq_of_lt hs] at he
        omega
      · rw [Nat.mod_eq_sub_mod (show length ≤ first + k by omega),
          Nat.mod_eq_of_lt (show first + k - length < length by omega)] at he
        omega

private theorem wordWindow_iff {length first last point : ℕ}
    (hf : first < length) (hl : last < length) (hp : point < length) :
    (∃ k, k < wordDistance length first last ∧ (first + (k + 1)) % length = point) ↔
      if first ≤ last then first < point ∧ point ≤ last else first < point ∨ point ≤ last := by
  unfold wordDistance
  split_ifs with h
  · constructor
    · rintro ⟨k, hk, he⟩
      rw [Nat.mod_eq_of_lt (show first + (k + 1) < length by omega)] at he
      omega
    · rintro ⟨hfirst, hlast⟩
      refine ⟨point - first - 1, by omega, ?_⟩
      rw [show first + (point - first - 1 + 1) = point by omega, Nat.mod_eq_of_lt hp]
  · constructor
    · rintro ⟨k, hk, he⟩
      by_cases hs : first + (k + 1) < length
      · rw [Nat.mod_eq_of_lt hs] at he
        exact Or.inl (by omega)
      · rw [Nat.mod_eq_sub_mod (show length ≤ first + (k + 1) by omega),
          Nat.mod_eq_of_lt (show first + (k + 1) - length < length by omega)] at he
        exact Or.inr (by omega)
    · rintro (hfirst | hlast)
      · refine ⟨point - first - 1, by omega, ?_⟩
        rw [show first + (point - first - 1 + 1) = point by omega, Nat.mod_eq_of_lt hp]
      · refine ⟨length - first + point - 1, by omega, ?_⟩
        rw [show first + (length - first + point - 1 + 1) = length + point by omega,
          Nat.add_mod, Nat.mod_self, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hp]

variable {G : Graph} (r : RotationSystem G) (word : List (Dart G)) (hn : word.Nodup)
  (hr : r.rotate = word.formPerm)

include hn hr

private theorem word_pow_eq_iff {a b : Dart G} (ha : a ∈ word) (hb : b ∈ word) (n : ℕ) :
    (r.rotate ^ n) a = b ↔ (word.idxOf a + n) % word.length = word.idxOf b := by
  have hi := List.idxOf_lt_length_of_mem ha
  have hj := List.idxOf_lt_length_of_mem hb
  have hpow := List.formPerm_pow_apply_getElem word hn n (word.idxOf a) hi
  rw [List.getElem_idxOf] at hpow
  rw [hr, hpow]
  constructor
  · intro he
    have hh := congrArg word.idxOf he
    simpa only [hn.idxOf_getElem] using hh
  · intro he
    simpa only [he] using List.getElem_idxOf hj

/-- The first literal rotation hit is the forward cyclic difference of the original word indices. -/
theorem rotationDistance_eq_word {a b : Dart G} (ha : a ∈ word) (hb : b ∈ word)
    (hv : a.vertex = b.vertex) :
    r.rotationDistance a b = if word.idxOf a ≤ word.idxOf b then word.idxOf b - word.idxOf a
      else word.length - word.idxOf a + word.idxOf b := by
  have hs := wordDistance_spec (List.idxOf_lt_length_of_mem ha) (List.idxOf_lt_length_of_mem hb)
  apply r.rotationDistance_eq a b hv
  · exact (word_pow_eq_iff r word hn hr ha hb _).mpr hs.2.1
  · intro k hk he
    exact hs.2.2 k hk ((word_pow_eq_iff r word hn hr ha hb k).mp he)

/-- Membership in a literal rotation interval is the corresponding cyclic index window. -/
theorem mem_rotationInterval_iff_word {a b c : Dart G}
    (ha : a ∈ word) (hb : b ∈ word) (hc : c ∈ word) (hv : a.vertex = b.vertex) :
    c ∈ r.rotationInterval a b ↔
      if word.idxOf a ≤ word.idxOf b then word.idxOf a < word.idxOf c ∧ word.idxOf c ≤ word.idxOf b
      else word.idxOf a < word.idxOf c ∨ word.idxOf c ≤ word.idxOf b := by
  classical
  rw [rotationInterval, rotationDistance_eq_word r word hn hr ha hb hv]
  have hmem : (∃ k, k < wordDistance word.length (word.idxOf a) (word.idxOf b) ∧
      (word.idxOf a + (k + 1)) % word.length = word.idxOf c) ↔
      c ∈ (Finset.range (wordDistance word.length (word.idxOf a) (word.idxOf b))).image
        (fun k => (r.rotate ^ (k + 1)) a) := by
    simp only [Finset.mem_image, Finset.mem_range, word_pow_eq_iff r word hn hr ha hc]
  exact hmem.symm.trans (wordWindow_iff (List.idxOf_lt_length_of_mem ha)
    (List.idxOf_lt_length_of_mem hb) (List.idxOf_lt_length_of_mem hc))

/-- Strictly interlaced original word indices are alternating passages in the actual rotation. -/
theorem alternates_of_word_crossing {a b c d : Dart G}
    (ha : a ∈ word) (hb : b ∈ word) (hc : c ∈ word) (hd : d ∈ word)
    (hab : a.vertex = b.vertex) (hcd : c.vertex = d.vertex) (hac : a.vertex = c.vertex)
    (hcross : min (word.idxOf a) (word.idxOf b) < min (word.idxOf c) (word.idxOf d) ∧
      min (word.idxOf c) (word.idxOf d) < max (word.idxOf a) (word.idxOf b) ∧
      max (word.idxOf a) (word.idxOf b) < max (word.idxOf c) (word.idxOf d)) :
    r.Alternates a b c d := by
  have haI := mem_rotationInterval_iff_word r word hn hr hc hd ha hcd
  have hbI := mem_rotationInterval_iff_word r word hn hr hc hd hb hcd
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hab, hcd, hac, ?_⟩
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · intro he
    have hh := congrArg word.idxOf he
    omega
  · by_cases horder : word.idxOf c ≤ word.idxOf d
    · rw [ite_eq_left horder] at haI hbI
      rw [haI, hbI]
      omega
    · rw [ite_eq_right horder] at haI hbI
      rw [haI, hbI]
      omega

end PushPuzzle.Graph.RotationSystem

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List.AdjacentTrace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryDiv
import CslibFrontier.Foundations.Data.List.Lookup
import CslibFrontier.Foundations.Data.Nat.Div

/-! Actual payload sorting retains every original occurrence through binary decorated keys. -/

public section

namespace PushPuzzle.PushS.Comb.Sort


open Turing.MultiTapeTM
open scoped Cslib.AdjacentSortTrace

/-- Original position breaks equal-key ties in the actual explicit list. -/
@[expose] def keys {α : Type} (key : α → ℕ) (xs : List α) : List ℕ :=
  xs.zipIdx.map fun p => key p.1 * (xs.length + 1) + p.2

/-- Sort the binary decorated keys with the library algorithm and read back the original payloads. -/
@[expose] def run {α : Type} (key : α → ℕ) (fallback : α) (xs : List α) : List α :=
  (Cslib.AdjacentSortTrace.compute (keys key xs)).sortedKeys.map fun k =>
    xs.getD (k % (xs.length + 1)) fallback

private theorem packed_mod (key n i : ℕ) (hi : i < n + 1) :
    (key * (n + 1) + i) % (n + 1) = i := by
  rw [Nat.mul_comm key (n + 1), Nat.mul_add_mod, Nat.mod_eq_of_lt hi]

private theorem decode_keys {α : Type} (key : α → ℕ) (fallback : α) (xs : List α) :
    (keys key xs).map (fun k => xs.getD (k % (xs.length + 1)) fallback) = xs := by
  calc
    _ = xs.zipIdx.map (fun p => xs.getD p.2 fallback) := by
      simp only [keys, List.map_map]
      apply List.map_congr_left
      intro p hp
      have hi : p.2 < xs.length + 1 := by have := List.snd_lt_of_mem_zipIdx hp; omega
      exact congrArg (fun i => xs.getD i fallback) (packed_mod _ _ _ hi)
    _ = xs := List.map_getD_zipIdx xs xs fallback rfl

/-- The actual sorter retains every source occurrence exactly once. -/
theorem run_perm {α : Type} (key : α → ℕ) (fallback : α) (xs : List α) :
    (run key fallback xs).Perm xs := by
  have hp := List.perm_insertionSort (· ≤ ·) (keys key xs)
  rw [← (Cslib.AdjacentSortTrace.components_compute (keys key xs)).1] at hp
  have hm := hp.map (fun k => xs.getD (k % (xs.length + 1)) fallback)
  rw [decode_keys] at hm
  exact hm

private theorem decoded_key {α : Type} (key : α → ℕ) (fallback : α) (xs : List α)
    {k : ℕ} (hk : k ∈ keys key xs) :
    key (xs.getD (k % (xs.length + 1)) fallback) = k / (xs.length + 1) := by
  obtain ⟨⟨a, i⟩, hai, rfl⟩ := List.mem_map.mp hk
  have hi : i < xs.length + 1 := by have := List.snd_lt_of_mem_zipIdx hai; omega
  have hget : xs[i]? = some a := List.mem_zipIdx_iff_getElem?.mp hai
  rw [packed_mod _ _ _ hi, Nat.mul_add_div_of_lt _ hi]
  simp only [List.getD_eq_getElem?_getD, hget, Option.getD_some]

/-- The emitted payload order is nondecreasing in the supplied original key. -/
theorem run_pairwise {α : Type} (key : α → ℕ) (fallback : α) (xs : List α) :
    (run key fallback xs).Pairwise (fun a b => key a ≤ key b) := by
  have hp := List.perm_insertionSort (· ≤ ·) (keys key xs)
  have hs := List.pairwise_insertionSort (· ≤ ·) (keys key xs)
  rw [← (Cslib.AdjacentSortTrace.components_compute (keys key xs)).1] at hp hs
  change List.Pairwise _ (List.map _ _)
  rw [List.pairwise_map]
  apply List.Pairwise.imp_of_mem _ hs
  intro a b ha hb hab
  rw [decoded_key key fallback xs (hp.mem_iff.mp ha), decoded_key key fallback xs (hp.mem_iff.mp hb)]
  exact Nat.div_le_div_right hab

private theorem keys_polyTime {α : Type} (enc : α ↪ List Bool) {key : α → ℕ}
    (hk : ComputableInPolyTime key enc encNat) :
    ComputableInPolyTime (keys key) (encList enc) (encList encNat) := by
  unfold keys
  apply ComputableInPolyTime.mapWithInput (ComputableInPolyTime.zipIdx enc)
  have hi : ComputableInPolyTime (fun p : List α × (α × ℕ) => p.2.2)
      (encPair (encList enc) (encPair enc encUnary)) encNat :=
    ComputableInPolyTime.unary_to_binary.comp (by fun_prop)
  fun_prop

/-- Binary key sorting and bounded binary payload lookup give the actual standard PT algorithm. -/
@[fun_prop] theorem computableInPolyTime_run {α : Type} (enc : α ↪ List Bool) {key : α → ℕ}
    (hk : ComputableInPolyTime key enc encNat) (fallback : α) :
    ComputableInPolyTime (run key fallback) (encList enc) (encList enc) := by
  have hkeys := keys_polyTime enc hk
  have hsort := Cslib.AdjacentSortTrace.computableInPolyTime_compute.comp hkeys
  have hordered : ComputableInPolyTime
      (fun xs => (Cslib.AdjacentSortTrace.compute (keys key xs)).sortedKeys)
      (encList enc) (encList encNat) := by fun_prop
  unfold run
  apply ComputableInPolyTime.mapWithInput hordered
  apply ComputableInPolyTime.listGetD_binary fallback (by fun_prop)
  apply ComputableInPolyTime.binary_mod' (by fun_prop) (by fun_prop)

end PushPuzzle.PushS.Comb.Sort

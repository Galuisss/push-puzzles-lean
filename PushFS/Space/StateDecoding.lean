/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Space.StateCode
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Mathlib.Data.List.GetD
import Mathlib.Data.List.FinRange
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-! Polynomial-time syntax checking and semantic reconstruction of state words. -/

@[expose] public section

namespace PushPuzzle.PushFS


open Turing.MultiTapeTM

namespace State

private theorem ofFn_getD {α : Type} (l : List α) (fallback : α) (n : ℕ)
    (hlen : l.length = n) : List.ofFn (fun i : Fin n => l.getD i fallback) = l := by
  apply List.ext_getElem (by simp only [List.length_ofFn]; exact hlen.symm)
  intro i hi hj
  simp only [List.getElem_ofFn]
  exact List.getD_eq_getElem _ _ hj

variable {w h : ℕ}

@[simp] theorem index_cellAt (i : Fin (h * w)) :
    finProdFinEquiv (cellAt i).swap = i := by
  change finProdFinEquiv (finProdFinEquiv.symm i) = i
  exact finProdFinEquiv.apply_symm_apply i

/-- Read the box half using the inverse row-major index. -/
def readBoxes (w h : ℕ) (word : List Bool) : Finset (Cell w h) :=
  Finset.univ.filter fun p =>
    (word.take (w * h)).getD (finProdFinEquiv p.swap).val false = true

/-- Player marker indices in the second half. -/
def readPlayers (w h : ℕ) (word : List Bool) : Finset (Fin (h * w)) :=
  Finset.univ.filter fun i => (word.drop (w * h)).getD i false = true

private theorem readPlayers_bits (s : State w h) :
    readPlayers w h s.bits = {finProdFinEquiv s.player.swap} := by
  have ht : s.bits.drop (w * h) = s.playerBits := by simp [bits]
  ext i
  simp only [readPlayers, Finset.mem_filter, Finset.mem_univ, true_and, ht,
    Finset.mem_singleton]
  rw [List.getD_eq_getElem _ _ (by
    simp only [playerBits, List.length_ofFn]
    exact i.isLt)]
  simp only [playerBits, List.getElem_ofFn, decide_eq_true_eq, cellAt_eq_iff]

/-- A uniform, nondependent check for any area and raw state word. -/
def codeValid (p : ℕ × List Bool) : Bool :=
  decide (p.2.length = 2 * p.1) && decide ((p.2.drop p.1).countP id = 1)

theorem countP_ofFn {n : ℕ} (f : Fin n → Bool) :
    (List.ofFn f).countP id = (Finset.univ.filter fun i => f i = true).card := by
  rw [List.ofFn_eq_map, List.countP_map]
  have hc := (List.nodup_finRange n).card_eq_countP (P := fun i => f i = true)
  simpa [Function.comp_def] using hc.symm

private theorem count_readPlayers (word : List Bool) (hlen : word.length = 2 * (w * h)) :
    (readPlayers w h word).card = (word.drop (w * h)).countP id := by
  have hn : (word.drop (w * h)).length = h * w := by
    simp only [List.length_drop, hlen, Nat.mul_comm h w]
    omega
  have ht := ofFn_getD (word.drop (w * h)) false (h * w) hn
  rw [← ht, countP_ofFn]
  rfl

private theorem boxBits_rebuild (word : List Bool) (p : Cell w h)
    (hlen : word.length = 2 * (w * h)) :
    (State.mk p (readBoxes w h word)).boxBits = word.take (w * h) := by
  have hn : (word.take (w * h)).length = h * w := by
    simp only [List.length_take, hlen, Nat.mul_comm h w]
    omega
  calc
    _ = List.ofFn (fun i : Fin (h * w) => (word.take (w * h)).getD i false) := by
      simp only [boxBits, readBoxes, Finset.mem_filter, Finset.mem_univ,
        true_and, index_cellAt, Bool.decide_eq_true]
    _ = _ := ofFn_getD _ _ _ hn

private theorem playerBits_rebuild (word : List Bool) (i : Fin (h * w))
    (bs : Finset (Cell w h)) (hlen : word.length = 2 * (w * h))
    (hp : readPlayers w h word = {i}) :
    (State.mk (cellAt i) bs).playerBits = word.drop (w * h) := by
  have hn : (word.drop (w * h)).length = h * w := by
    simp only [List.length_drop, hlen, Nat.mul_comm h w]
    omega
  have hflag (j : Fin (h * w)) :
      decide (j = i) = (word.drop (w * h)).getD j false := by
    have hj := congrArg (fun fs : Finset (Fin (h * w)) => decide (j ∈ fs)) hp
    simpa [readPlayers] using hj.symm
  calc
    _ = List.ofFn (fun j : Fin (h * w) => (word.drop (w * h)).getD j false) := by
      simp only [playerBits, cellAt_eq_iff, index_cellAt, hflag]
    _ = _ := ofFn_getD _ _ _ hn

/-- A valid raw code represents a state, and every state has a valid raw code. -/
theorem codeValid_correct (word : List Bool) :
    codeValid (w * h, word) = true ↔ ∃ s : State w h, s.bits = word := by
  simp only [codeValid, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨hlen, hcount⟩
    have hc : (readPlayers w h word).card = 1 := by
      rw [count_readPlayers word hlen, hcount]
    obtain ⟨i, hi⟩ := Finset.card_eq_one.mp hc
    refine ⟨⟨cellAt i, readBoxes w h word⟩, ?_⟩
    change (State.mk (cellAt i) (readBoxes w h word)).boxBits ++
      (State.mk (cellAt i) (readBoxes w h word)).playerBits = word
    rw [boxBits_rebuild word _ hlen, playerBits_rebuild word i _ hlen hi]
    exact List.take_append_drop _ _
  · rintro ⟨s, rfl⟩
    refine ⟨length_bits s, ?_⟩
    rw [← count_readPlayers s.bits (length_bits s), readPlayers_bits]
    exact Finset.card_singleton _

open ComputableInPolyTime in
/-- The arbitrary-code check has one uniform machine certificate, with area
passed in unary. It never enumerates states or box subsets. -/
theorem codeValid_computable :
    ComputableInPolyTime codeValid (encPair encUnary encBits) encBool := by
  have hdrop : ComputableInPolyTime
      (fun p : ℕ × List Bool => p.2.drop p.1) (encPair encUnary encBits) encBits := by
    fun_prop
  have hcount : ComputableInPolyTime
      (fun p : ℕ × List Bool => (p.2.drop p.1).countP id)
      (encPair encUnary encBits) encUnary :=
    countPWith (encP := encBool) (encA := encBool) (test := fun p => p.2)
      (snd _ _) (const false) hdrop
  unfold codeValid
  fun_prop

end State

end PushPuzzle.PushFS

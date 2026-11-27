/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Chain.Movement

/-! Both full phase changes are built by actual block updates and hub walks.
Eastward propagation updates right-to-left; the inverse order updates left-to-right. -/

@[expose] public section

namespace PushPuzzle.PushFS.Gadgets.Wires.Chain



set_option maxRecDepth 4096

def cut (n t : ℕ) : Phases n := fun i => decide (t ≤ i.val)
def uniform (n : ℕ) (a : Bool) : Phases n := fun _ => a

theorem cut_zero (n : ℕ) : cut n 0 = uniform n true := by funext i; simp [cut,uniform]
theorem cut_finish (n : ℕ) : cut n (blockCount n) = uniform n false := by
  funext i
  simp only [cut,uniform,decide_eq_false_iff_not]
  exact Nat.not_le_of_gt i.isLt

theorem cut_frontier (n : ℕ) (i : Block n) : Frontier n (cut n i.val) i := by
  constructor
  · intro j hj
    simp only [cut,decide_eq_false_iff_not]
    exact Nat.not_le_of_gt hj
  · intro j hj
    simp only [cut,decide_eq_true_eq]
    exact Nat.le_of_lt hj

theorem cut_next_frontier (n : ℕ) (i : Block n) : Frontier n (cut n (i.val+1)) i := by
  constructor
  · intro j hj
    simp only [cut,decide_eq_false_iff_not]
    change j.val < i.val at hj
    omega
  · intro j hj
    simp only [cut,decide_eq_true_eq]
    exact hj

theorem update_cut_false (n : ℕ) (i : Block n) : Function.update (cut n i.val) i false = cut n (i.val+1) := by
  funext j
  by_cases hij : j = i
  · subst j
    simp [Function.update_self,cut]
  · rw [Function.update_of_ne hij]
    apply Bool.eq_iff_iff.mpr
    simp only [cut,decide_eq_true_eq]
    have hv : j.val ≠ i.val := fun hh => hij (Fin.ext hh)
    omega

theorem update_cut_true (n : ℕ) (i : Block n) : Function.update (cut n (i.val+1)) i true = cut n i.val := by
  funext j
  by_cases hij : j = i
  · subst j
    simp [Function.update_self,cut]
  · rw [Function.update_of_ne hij]
    apply Bool.eq_iff_iff.mpr
    simp only [cut,decide_eq_true_eq]
    have hv : j.val ≠ i.val := fun hh => hij (Fin.ext hh)
    omega

end PushPuzzle.PushFS.Gadgets.Wires.Chain

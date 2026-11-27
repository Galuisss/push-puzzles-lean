/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Run
public import Mathlib.Data.Fin.Basic

/-! Concatenating real horizontal and vertical macrocell walks through the rectangular source grid. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.MeshWalking

variable {W H m n : ℕ}

private theorem rectangle (B : Board W H) (node : Fin (m+1)→Fin (n+1)→State W H)
    (hh : ∀x : Fin m,∀y,Reachable B (some 1) (node x.castSucc y) (node x.succ y) ∧
      Reachable B (some 1) (node x.succ y) (node x.castSucc y))
    (hv : ∀x,∀y : Fin n,Reachable B (some 1) (node x y.castSucc) (node x y.succ) ∧
      Reachable B (some 1) (node x y.succ) (node x y.castSucc)) (x : Fin (m+1)) (y : Fin (n+1)) :
    Reachable B (some 1) (node 0 0) (node x y) ∧Reachable B (some 1) (node x y) (node 0 0) := by
  have row (i : Fin (m+1)) : Reachable B (some 1) (node 0 0) (node i 0) ∧
      Reachable B (some 1) (node i 0) (node 0 0) := by
    induction i using Fin.induction with
    | zero=>exact ⟨.refl,.refl⟩
    | succ i ih=>exact ⟨ih.1.trans (hh i 0).1,(hh i 0).2.trans ih.2⟩
  have col (j : Fin (n+1)) : Reachable B (some 1) (node x 0) (node x j) ∧
      Reachable B (some 1) (node x j) (node x 0) := by
    induction j using Fin.induction with
    | zero=>exact ⟨.refl,.refl⟩
    | succ j ih=>exact ⟨ih.1.trans (hv x j).1,(hv x j).2.trans ih.2⟩
  exact ⟨(row x).1.trans (col y).1,(col y).2.trans (row x).2⟩

theorem rectangle_positive (hm : 0<m) (hn : 0<n) (B : Board W H)
    (node : Fin m→Fin n→State W H)
    (hh : ∀x : Fin m,∀hx : x.val+1<m,∀y,
      Reachable B (some 1) (node x y) (node ⟨x.val+1,hx⟩ y) ∧
      Reachable B (some 1) (node ⟨x.val+1,hx⟩ y) (node x y))
    (hv : ∀x,∀y : Fin n,∀hy : y.val+1<n,
      Reachable B (some 1) (node x y) (node x ⟨y.val+1,hy⟩) ∧
      Reachable B (some 1) (node x ⟨y.val+1,hy⟩) (node x y)) (x : Fin m) (y : Fin n) :
    Reachable B (some 1) (node ⟨0,hm⟩ ⟨0,hn⟩) (node x y) ∧
      Reachable B (some 1) (node x y) (node ⟨0,hm⟩ ⟨0,hn⟩) := by
  cases m with
  | zero=>omega
  | succ m=>
    cases n with
    | zero=>omega
    | succ n=>
      exact rectangle B node (fun i j=>hh i.castSucc (by change i.val+1<m+1; omega) j)
        (fun i j=>hv i j.castSucc (by change j.val+1<n+1; omega)) x y

end PushPuzzle.PushFS.Reduction.MeshWalking

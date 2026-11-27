/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Run

/-! A finite sequence of actual primitive updates advances each selected physical owner once. -/

@[expose] public section
namespace PushPuzzle.PushFS.Reduction.ProfileSweep


open scoped Classical
variable {α : Type} {n W H : ℕ}

noncomputable def stage (node : Fin n→α) (base : α→Bool) (t : ℕ) : α→Bool :=
  fun i=>if ∃j : Fin n,j.val<t ∧node j=i then true else base i

private theorem zero (node : Fin n→α) (base : α→Bool) : stage node base 0=base := by
  funext i
  simp only [stage,Nat.not_lt_zero,false_and,exists_false,ite_false]

theorem node_true (node : Fin n→α) (base : α→Bool) (t : ℕ) (j : Fin n) (hj : j.val<t) :
    stage node base t (node j)=true := ite_eq_left ⟨j,hj,rfl⟩

theorem node_false (node : Fin n→α) (hinj : Function.Injective node) (base : α→Bool)
    (hbase : ∀j,base (node j)=false) (t : ℕ) (j : Fin n) (hj : t≤j.val) :
    stage node base t (node j)=false := by
  have hn : ¬∃k : Fin n,k.val<t ∧node k=node j := by
    rintro ⟨k,hk,he⟩
    have he':=hinj he
    subst k
    omega
  exact (ite_eq_right hn).trans (hbase j)

theorem outside (node : Fin n→α) (base : α→Bool) (t : ℕ) (i : α) (hi : ∀j,node j≠i) :
    stage node base t i=base i := by
  apply ite_eq_right
  rintro ⟨j,_,he⟩
  exact hi j he

theorem step [DecidableEq α] (node : Fin n→α) (base : α→Bool) (j : Fin n) :
    Function.update (stage node base j.val) (node j) true=stage node base (j.val+1) := by
  funext i
  by_cases hi : i=node j
  · subst i
    rw [Function.update_self,node_true node base (j.val+1) j (Nat.lt_succ_self _)]
  · rw [Function.update_of_ne hi]
    unfold stage
    have he : (∃k : Fin n,k.val<j.val+1 ∧node k=i) ↔∃k : Fin n,k.val<j.val ∧node k=i := by
      constructor
      · rintro ⟨k,hk,he⟩
        have hne : k.val≠j.val := by
          intro hh
          have hh':k=j :=Fin.ext hh
          subst k
          exact hi he.symm
        exact ⟨k,by omega,he⟩
      · rintro ⟨k,hk,he⟩
        exact ⟨k,by omega,he⟩
    by_cases hs : ∃k : Fin n,k.val<j.val ∧node k=i
    · have hl:=he.mpr hs
      simp only [ite_eq_left hs,ite_eq_left hl]
    · have hl:=mt he.mp hs
      simp only [ite_eq_right hs,ite_eq_right hl]

/-- Concatenate real complete macros in their stated owner order. -/
theorem replay (node : Fin n→α) (base : α→Bool) (state : (α→Bool)→State W H)
    (B : Board W H) (hs : ∀j : Fin n,Reachable B (some 1) (state (stage node base j.val))
      (state (stage node base (j.val+1)))) :
    Reachable B (some 1) (state base) (state (stage node base n)) := by
  have all (t : Fin (n+1)) : Reachable B (some 1) (state (stage node base 0)) (state (stage node base t.val)) := by
    induction t using Fin.induction with
    | zero=>exact .refl
    | succ j ih=>exact ih.trans (hs j)
  have hh:=all (Fin.last n)
  rw [zero] at hh
  exact hh

end PushPuzzle.PushFS.Reduction.ProfileSweep

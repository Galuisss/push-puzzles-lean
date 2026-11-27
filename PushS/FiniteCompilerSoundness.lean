/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCompilerCertificate
public import PushS.FiniteSourceSoundness

/-! Every successful output of the actual total finite-force compiler reflects its original NCL instance. -/

public section
namespace PushPuzzle.PushS.FiniteCompiler

open PushFS PushFS.Reduction
open Cslib.Complexity.NCL

theorem mem_of_walled_solvable (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance)
    {cap : Option ℕ} (hsol : (walled w hw x).Solvable cap) : x ∈ PlaneWordAndOrNCL := by
  by_cases h : PhysicalCompiler.checkedGuard x = true
  · have hx := (PhysicalCompiler.checkedGuard_spec x).mp h
    rw [walled,dite_eq_left h] at hsol
    refine ⟨hx.plane,hx.typed,hx.valid,hx.initial_width,hx.target_width,?_,?_⟩
    · exact (AndOrGraph.checkLegal_eq_true_iff _ hx.valid.1 _).mp hx.initial_legal
    · exact FiniteSourceInventory.ncl_of_solvable w hw (PhysicalCompiler.source x) hx.valid hx.plane hx.typed
        hx.initial_legal hx.target_legal hsol
  · rw [walled,dite_eq_right h] at hsol
    exact False.elim (reject_not_solvable cap hsol)

theorem mem_of_compile_solvable (k : ℕ) (hk : 1 ≤ k) (x : PlaneWordAndOrNCL.Instance)
    (hsol : (compile (k+1) (by omega) x).SolvableFinite k) : x ∈ PlaneWordAndOrNCL :=
  mem_of_walled_solvable (k+1) (by omega) x ((compile_solvable_iff k hk x).mp hsol)

end PushPuzzle.PushS.FiniteCompiler

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCompiler
public import PushS.FiniteSourceCertificate

/-! C1–C3 for the compiler's walled stage and transfer to single-box solvability. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteCompiler

open PushFS PushFS.Reduction
open Cslib.Complexity.NCL

theorem walled_certificate (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) :
    Certificate (walled w hw x) := by
  by_cases h : PhysicalCompiler.checkedGuard x = true
  · rw [walled,dite_eq_left h]
    exact FiniteSourceInventory.certificate w hw _ _ _
  · rw [walled,dite_eq_right h]
    exact reject_certificate

private theorem walled_solvable_iff_one (w : ℕ) (hw : 2 ≤ w) (k : ℕ) (hk : 1 ≤ k)
    (x : PlaneWordAndOrNCL.Instance) :
    (walled w hw x).Solvable (some k) ↔ (walled w hw x).Solvable (some 1) :=
  (walled_certificate w hw x).solvable_iff_one hk

theorem compile_solvable_iff_one (k : ℕ) (hk : 1 ≤ k) (x : PlaneWordAndOrNCL.Instance) :
    (compile (k+1) (by omega) x).SolvableFinite k ↔ (walled (k+1) (by omega) x).Solvable (some 1) :=
  (compile_solvable_iff k hk x).trans (walled_solvable_iff_one (k+1) (by omega) k hk x)

end PushPuzzle.PushS.FiniteCompiler

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalCertificate
public import PushFS.Reduction.PhysicalCompiler

/-! All outputs of the total physical compiler satisfy C1–C3 for every push force. -/

@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalCompiler

open Cslib.Complexity.NCL

private theorem compile_certificate (x : PlaneWordAndOrNCL.Instance) : Certificate (compile x) := by
  by_cases h : guard x=true
  · rw [compile,dite_eq_left h]
    exact PhysicalInventory.certificate (source x) ((guard_spec x).mp h).1 ((guard_spec x).mp h).2
  · rw [compile,dite_eq_right h]
    exact reject_certificate

private theorem checkedCompile_certificate (x : PlaneWordAndOrNCL.Instance) : Certificate
    (checkedCompile x) := by
  by_cases h : checkedGuard x=true
  · rw [checkedCompile,ite_eq_left h]
    exact compile_certificate x
  · rw [checkedCompile,ite_eq_right h]
    exact reject_certificate

theorem checkedCompile_unlimited_iff_one (x : PlaneWordAndOrNCL.Instance) :
    (checkedCompile x).Solvable none ↔(checkedCompile x).Solvable (some 1) :=
  (checkedCompile_certificate x).solvable_unlimited_iff_one

theorem checkedCompile_finite_iff_one (x : PlaneWordAndOrNCL.Instance) (k : ℕ) (hk : 1≤k) :
    (checkedCompile x).Solvable (some k) ↔(checkedCompile x).Solvable (some 1) :=
  (checkedCompile_certificate x).solvable_iff_one (by simpa using hk)

end PushPuzzle.PushFS.Reduction.PhysicalCompiler

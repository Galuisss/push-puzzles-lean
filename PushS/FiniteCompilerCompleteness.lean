/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCompilerSoundness
public import PushS.FiniteSourceActualGeometry
public import PushS.FiniteSourceForwardBits

/-! Exact source-language correctness of the total wall-free finite-force compiler. -/

public section
namespace PushPuzzle.PushS.FiniteCompiler

open PushFS PushFS.Reduction
open Cslib.Complexity.NCL

private theorem walled_complete (w : ℕ) (hw : 2 ≤ w) {x : PlaneWordAndOrNCL.Instance}
    (hx : x ∈ PlaneWordAndOrNCL) : (walled w hw x).Solvable (some 1) := by
  have hc := PhysicalCompiler.checks_of_mem hx
  obtain ⟨_,_,_,_,_,_,hr⟩ := hx
  rw [walled_eq w hw x hc]
  exact FiniteSourceInventory.checkedPuzzle_solvable_of_bits w hw x.word hc.valid hc.plane hc.typed
    x.initial x.target hc.initial_width hc.target_width
    (fun f e hf he => FiniteSourceInventory.actualEdgeGeometry w hw x.word hc.valid hc.plane hc.typed
      f e x.target hf he) hr

private theorem walled_iff_one (w : ℕ) (hw : 2 ≤ w) (x : PlaneWordAndOrNCL.Instance) :
    x ∈ PlaneWordAndOrNCL ↔ (walled w hw x).Solvable (some 1) :=
  ⟨walled_complete w hw,mem_of_walled_solvable w hw x⟩

theorem compile_complete (k : ℕ) (hk : 1 ≤ k) {x : PlaneWordAndOrNCL.Instance}
    (hx : x ∈ PlaneWordAndOrNCL) : (compile (k+1) (by omega) x).SolvableFinite k :=
  (compile_solvable_iff_one k hk x).mpr ((walled_iff_one (k+1) (by omega) x).mp hx)

theorem compile_iff_finite (k : ℕ) (hk : 1 ≤ k) (x : PlaneWordAndOrNCL.Instance) :
    x ∈ PlaneWordAndOrNCL ↔ (compile (k+1) (by omega) x).SolvableFinite k :=
  ⟨compile_complete k hk,mem_of_compile_solvable k hk x⟩

end PushPuzzle.PushS.FiniteCompiler

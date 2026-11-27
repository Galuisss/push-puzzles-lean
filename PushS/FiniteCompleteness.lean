/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteCompilerCompleteness
public import PushS.FiniteUpperBound
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Hardness

/-! Standard PSPACE-completeness of wall-free Push-kS for every fixed positive push cap. -/

public section
namespace PushPuzzle.PushS

open Cslib.Complexity Cslib.Complexity.NCL

/-- The actual thick-block compiler gives a standard dense polynomial-time reduction to Push-kS. -/
theorem polyTimeReducible_PlaneWordAndOrNCL_finite (k : ℕ) (hk : 1 ≤ k) :
    PolyTimeReducible encPlaneWordAndOrNCL encoding PlaneWordAndOrNCL (solvableFinite k) :=
  ⟨FiniteCompiler.compile (k+1) (by omega),FiniteCompiler.compile_polyTime (k+1) (by omega),
    FiniteCompiler.compile_iff_finite k hk⟩

/-- Wall-free Push-kS is PSPACE-hard for every fixed k≥1. -/
theorem solvableFinite_pspaceHard (k : ℕ) (hk : 1 ≤ k) : PSPACEHard encoding (solvableFinite k) :=
  PlaneWordAndOrNCL_pspaceHard.trans (polyTimeReducible_PlaneWordAndOrNCL_finite k hk)

/-- Wall-free Push-kS is PSPACE-complete for every fixed k≥1. -/
theorem solvableFinite_pspaceComplete (k : ℕ) (hk : 1 ≤ k) : PSPACEComplete encoding (solvableFinite k) :=
  ⟨solvableFinite_mem_PSPACE k,solvableFinite_pspaceHard k hk⟩

end PushPuzzle.PushS

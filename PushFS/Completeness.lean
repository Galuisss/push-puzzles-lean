/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalForward
public import PushFS.Reduction.PhysicalReverse
public import PushFS.Reduction.CompilerCertificate
public import PushFS.UpperBound
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.PlaneWord.Hardness

/-! Standard PSPACE completeness of Push-1FS, every fixed Push-kFS with k≥1, and Push-*FS. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS

open Cslib.Complexity.NCL Reduction.PhysicalCompiler

/-- The total complete physical compiler preserves exactly the source language. -/
private theorem Reduction.PhysicalCompiler.checkedCompile_iff_one (x : PlaneWordAndOrNCL.Instance) :
    x∈PlaneWordAndOrNCL ↔(checkedCompile x).Solvable (some 1) :=
  ⟨checkedCompile_complete,checkedCompile_sound⟩

/-- The compiler preserves source membership for each fixed positive push cap. -/
private theorem Reduction.PhysicalCompiler.checkedCompile_iff_finite
    (x : PlaneWordAndOrNCL.Instance) (k : ℕ) (hk : 1≤k) :
    x∈PlaneWordAndOrNCL ↔(checkedCompile x).Solvable (some k) :=
  (checkedCompile_iff_one x).trans (checkedCompile_finite_iff_one x k hk).symm

/-- The compiler preserves source membership with unlimited pushing. -/
private theorem Reduction.PhysicalCompiler.checkedCompile_iff_unlimited
    (x : PlaneWordAndOrNCL.Instance) :
    x∈PlaneWordAndOrNCL ↔(checkedCompile x).Solvable none :=
  (checkedCompile_iff_one x).trans (checkedCompile_unlimited_iff_one x).symm

/-- The actual checked physical compiler is a standard polynomial-time reduction to Push-1FS. -/
private theorem polyTimeReducible_PlaneWordAndOrNCL_one :
    PolyTimeReducible encPlaneWordAndOrNCL encoding PlaneWordAndOrNCL (solvable (some 1)) :=
  ⟨checkedCompile,checkedCompile_polyTime,checkedCompile_iff_one⟩

/-- The same complete physical boards give a standard reduction to each fixed positive push cap. -/
private theorem polyTimeReducible_PlaneWordAndOrNCL_finite (k : ℕ) (hk : 1≤k) :
    PolyTimeReducible encPlaneWordAndOrNCL encoding PlaneWordAndOrNCL (solvable (some k)) :=
  ⟨checkedCompile,checkedCompile_polyTime,fun x=>checkedCompile_iff_finite x k hk⟩

/-- The same complete physical boards give the standard reduction to unlimited pushing. -/
private theorem polyTimeReducible_PlaneWordAndOrNCL_unlimited :
    PolyTimeReducible encPlaneWordAndOrNCL encoding PlaneWordAndOrNCL (solvable none) :=
  ⟨checkedCompile,checkedCompile_polyTime,checkedCompile_iff_unlimited⟩

/-- Push-1FS is PSPACE-complete under the fixed dense instance encoding. -/
theorem solvable_one_pspaceComplete : PSPACEComplete encoding (solvable (some 1)) :=
  ⟨solvable_mem_PSPACE (some 1),PlaneWordAndOrNCL_pspaceHard.trans polyTimeReducible_PlaneWordAndOrNCL_one⟩

/-- Push-kFS is PSPACE-complete for every fixed k≥1. -/
theorem solvable_finite_pspaceComplete (k : ℕ) (hk : 1≤k) : PSPACEComplete encoding (solvable (some k)) :=
  ⟨solvable_mem_PSPACE (some k),PlaneWordAndOrNCL_pspaceHard.trans (polyTimeReducible_PlaneWordAndOrNCL_finite k hk)⟩

/-- Push-*FS is PSPACE-complete. -/
theorem solvable_unlimited_pspaceComplete : PSPACEComplete encoding (solvable none) :=
  ⟨solvable_mem_PSPACE none,PlaneWordAndOrNCL_pspaceHard.trans polyTimeReducible_PlaneWordAndOrNCL_unlimited⟩

end PushPuzzle.PushFS

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteBasic
public import PushS.UpperBound

/-! Standard polynomial-space membership for wall-free finite pushing. -/

public section
namespace PushPuzzle.PushS

open Cslib.Complexity

/-- Forgetting the no-wall proof preserves the finite-cap storage language. -/
private theorem polyTimeReducible_finite (k : ℕ) :
    PolyTimeReducible encoding PushFS.encoding (solvableFinite k)
      (PushFS.solvable (some k)) :=
  ⟨Instance.toInstance, toInstance_polyTime, fun _ => Iff.rfl⟩

/-- Push-kS belongs to PSPACE for every fixed finite push cap. -/
theorem solvableFinite_mem_PSPACE (k : ℕ) : solvableFinite k ∈ PSPACE encoding :=
  (polyTimeReducible_finite k).mem_PSPACE (PushFS.solvable_mem_PSPACE (some k))

end PushPuzzle.PushS

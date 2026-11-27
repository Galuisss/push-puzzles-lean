/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Encoding
public import PushFS.UpperBound
public import CslibFrontier.Computability.Complexity.Classes.Space.Closure

/-! Polynomial-space reachability for wall-free unlimited pushing. -/

public section
namespace PushPuzzle.PushS

open Cslib.Complexity
open Turing.MultiTapeTM

/-- Forgetting the no-wall proof copies the unchanged explicit input word. -/
@[fun_prop] theorem toInstance_polyTime :
    ComputableInPolyTime Instance.toInstance encoding PushFS.encoding :=
  ComputableInPolyTime.of_eq fun _ => rfl

/-- The wall-free language reduces to the common unlimited storage semantics. -/
private theorem polyTimeReducible_unlimited :
    PolyTimeReducible encoding PushFS.encoding solvable (PushFS.solvable none) :=
  ⟨Instance.toInstance, toInstance_polyTime, fun _ => Iff.rfl⟩

/-- Push-*S belongs to PSPACE under its explicit dense rectangle encoding. -/
theorem solvable_mem_PSPACE : solvable ∈ PSPACE encoding :=
  polyTimeReducible_unlimited.mem_PSPACE (PushFS.solvable_mem_PSPACE none)

end PushPuzzle.PushS

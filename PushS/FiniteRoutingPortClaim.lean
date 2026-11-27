/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCompiler
public import PushFS.Reduction.CanonicalPhases

/-! The canonical inward port bit agrees with the source gate claim. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

theorem portInflow_eq_gateClaim (s : Gadgets.Gates.Signals) (role : Fin 3) :
    portInflow s.left s.upper s.right role = gateClaim s role := by
  fin_cases role <;> rfl

end PushPuzzle.PushS.FiniteRouting

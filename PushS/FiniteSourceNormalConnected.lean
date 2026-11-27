/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceMouthFree
public import PushS.FiniteSourceLegal

/-! Both complete exposed line lanes are connected under every actual normal primitive profile. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.LineSite

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem normal_outer_connected (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (north north' : Bool) (x y : Fin (Line.width w s.atoms))
    (hx : FiniteTools.radius w+1 ≤ x.val) (hx' : x.val ≤ FiniteTools.radius w+Line.span w s.atoms)
    (hy : FiniteTools.radius w+1 ≤ y.val) (hy' : y.val ≤ FiniteTools.radius w+Line.span w s.atoms) :
    Reachable (inventory w hw v).board (some 1)
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north x)))
      (PrimitiveProfile.state w hw v phase (s.actualEmbedding.cells (Line.outerCell w s.atoms north' y))) :=
  s.normal_connected_of_mouth_free (admissible w hw v hP hT) phase (s.normal_mouths_free hP hT phase)
    north north' x y hx hx' hy hy'

end PushPuzzle.PushS.FiniteSourceInventory.LineSite

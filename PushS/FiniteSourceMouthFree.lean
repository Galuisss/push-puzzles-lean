/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceActionFloor
public import PushS.FiniteSourceMouthStock
public import PushS.FiniteSourceNormalWalking
public import PushS.FiniteRoutingNormalMouths

/-! The mandatory first flip provides an actual free passage between both full-board outer lanes. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting

attribute [local irreducible] codes width height Line.width Line.height Line.walls

namespace LineSite

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (s : LineSite w hw v)

theorem normal_mouths_free (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) : s.MouthsFree phase := by
  intro j p hx hy hy' hside
  exact ⟨s.action_floor hP hT p (Line.program_first_mouth_active w hw (segmentLength s.code.segment)
    (s.code.above != s.code.desiredSide) s.code.above s.code.last j p hx hy hy' hside),
    s.normal_first_mouth_empty phase j p hx hy hy'⟩

end LineSite
end PushPuzzle.PushS.FiniteSourceInventory

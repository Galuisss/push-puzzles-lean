/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingCapSideStock
public import PushS.FiniteRoutingSideCollars

/-! Exposed line-side marks in a source collar avoid its literal normal-stock axis. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction

attribute [local irreducible] Line.width Line.height Line.walls FiniteTools.side FiniteGeometry.side

theorem local_cap_side_collar_off_lane (w : ℕ) (hw : 2 ≤ w) (code : CellPlan.Code) (c : LineCode)
    (hc : .line c ∈ FiniteSourceInventory.localCodes w code) {a : ℕ × ℕ}
    (hp : c.NearTrace w a) (ha : CapSideBand w c a) (face : Direction) (hf : InCollar w face a) :
    ¬SameLane face (Line.along w face (boundaryPoint w face) 0) a :=
  local_off_axis_collar_off_lane w hw code c hc hp ha.2 face hf

end PushPuzzle.PushS.FiniteRouting

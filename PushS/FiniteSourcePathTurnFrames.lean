/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceTurnActionFloor
public import PushS.FiniteSourceTurnActionStock
public import PushS.FiniteSourcePathForward

/-! Every actual path turn has its complete real-board action frame in each normal phase. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.PathSite

open PushFS PushFS.Reduction FiniteRouting
open scoped Classical

attribute [local irreducible] codes width height FiniteTools.side

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {P : PathSpec}

/-- The actual turn's floor and selected four-box ownership supply its entire event frame. -/
theorem turn_event_frame (s : PathSite w hw v P) (G : P.Geometry w) (E : s.Endpoints)
    (hb : P.target = !P.initial) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (phase : Fin (codes w v).length → Bool) (i : Fin P.segments.length) (hi : P.hasTurn i.val)
    (B : Board (width w v) (height w v)) (hB : B.walls = (inventory w hw v).walls) :
    s.EventFrame G E B phase (.turn i hi) := by
  refine ⟨?_,s.turn_fixed_avoids G hb hP hT phase i hi,?_⟩
  · intro p hp
    rw [hB]
    exact (s.turn G i hi).action_floor p hp
  · rw [hB]
    exact PrimitiveProfile.outside_floor (admissible w hw v hP hT) phase _

end PushPuzzle.PushS.FiniteSourceInventory.PathSite

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateMatching
public import PushS.FiniteRoutingInitial
import Mathlib.Tactic.FinCases

/-! All core normal-slot rails and support cells avoid every actual initial arm wall. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry FiniteGateMatching

attribute [local irreducible] FiniteGeometry.side Line.width Line.height Line.program

-- The finite box-family and port cases retain all scalar rail coordinates and both end supports.
set_option maxHeartbeats 1000000 in
/-- An AND rail cell in an initial arm's outward half-plane lies on that arm's literal working lane. -/
theorem andRail_outward_lane (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) (l : AndLabel w)
    (i : Fin (andTravel l+3))
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andLine w l i))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andLine w l i)) := by
  have hi := i.isLt
  fin_cases role <;> cases l <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,
      andLine,andLinePoint,andVertical,andTravel,andPoint,origin,coreOffset,padding,spacing] at * <;> omega

-- The four OR box families use four-point actual rails, including both end supports.
set_option maxHeartbeats 1000000 in
/-- An OR rail cell in an initial arm's outward half-plane lies on that arm's literal working lane. -/
theorem orRail_outward_lane (w : ℕ) (hw : 2 ≤ w) (role : Fin 3) (l : OrLabel w) (i : Fin 4)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orLine w l i))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orLine w l i)) := by
  have hi := i.isLt
  fin_cases role <;> cases l <;>
    simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,
      orLine,orLinePoint,orVertical,orPoint,origin,coreOffset,padding,spacing] at * <;> omega

end PushPuzzle.PushS.FiniteRouting

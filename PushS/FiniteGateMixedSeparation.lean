/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteGateState
public import PushS.FiniteRoutingInitial

/-! Every independent mixed core stock misses the exposed sides and deep mouths of each first arm. -/

public section
namespace PushPuzzle.PushS.FiniteRouting

open PushFS PushFS.Reduction FiniteGeometry FiniteGateState

attribute [local irreducible] FiniteGeometry.side Line.width Line.height
-- Mixed-cell coordinates reduce nested finite-label case trees.
set_option maxRecDepth 8192

/-- A mixed AND stock entering any outward arm half-plane lies on that arm's axis. -/
theorem andMixed_outward_lane (w : ℕ) (hw : 2 ≤ w) (X : AndPhases w) (role : Fin 3)
    (l : AndLabel w)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andMixedCell w X l))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w true role) 0)
      (coreWorld w (andMixedCell w X l)) := by
  cases l with
  | west i => exact andActor_outward_lane w hw _ _ _ role _ h
  | upper i => exact andActor_outward_lane w hw _ _ _ role _ h
  | lower i => exact andActor_outward_lane w hw _ _ _ role _ h
  | guard i => exact andActor_outward_lane w hw _ _ _ role _ h
  | branchB i => exact andActor_outward_lane w hw _ _ _ role _ h
  | branchC i => exact andActor_outward_lane w hw _ _ _ role _ h
  | middle =>
    have hh := X.middle.isLt
    fin_cases role <;>
      simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,andMixedCell,
        origin,coreOffset,padding,spacing] at * <;> omega
  | triggerA =>
    have hh := X.triggerA.isLt
    fin_cases role <;>
      simp [Outward,SameLane,PortAnnulus.innerDirection,Line.along,corePort,coreWorld,andMixedCell,
        origin,coreOffset,padding,spacing] at * <;> omega

/-- The corresponding literal outward-axis property for arbitrary OR branch phases. -/
theorem orMixed_outward_lane (w : ℕ) (hw : 2 ≤ w) (X : OrPhases w) (role : Fin 3)
    (l : OrLabel w)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orMixedCell w X l))) :
    SameLane (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w false role) 0)
      (coreWorld w (orMixedCell w X l)) := by
  cases l <;> exact orActor_outward_lane w hw _ _ _ role _ h

/-- Advancing one cell outward only strengthens the scalar-zero outward half-plane. -/
theorem outward_one_zero (w : ℕ) (kind : Bool) (role : Fin 3) (a : ℕ × ℕ)
    (h : Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) 1) a) :
    Outward (PortAnnulus.innerDirection role)
      (Line.along w (PortAnnulus.innerDirection role) (corePort w kind role) 0) a := by
  fin_cases role <;> cases kind <;>
    simp [Outward,PortAnnulus.innerDirection,Line.along,corePort,padding,spacing] at * <;> omega

end PushPuzzle.PushS.FiniteRouting

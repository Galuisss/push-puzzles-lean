/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreAccess
public import PushS.FiniteSourceGatePreparedTriggerFrames
public import PushS.FiniteSourceAndAFrames

/-! Concrete real-board context for one selected gate branch. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateFaceGeometry FiniteGateOuterAccess
open FiniteGateFaceBridge FiniteGateCanonicalAccess
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side

/-- Actual source metadata, selected-arm preparation and the same physical board at the current core update. -/
structure GatePhysicalContext {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)
    (role : Fin 3) (p : PathSite w hw v (armSpec w c.gate role)) (B : Board (width w v) (height w v)) where
  location : p.location = ((codes w v).get c.index).1
  plane : v.1.checkPlane = true
  typed : v.1.WellTyped [] []
  admissible : (inventory w hw v).Admissible
  phase : GridRouting.Point → Bool
  fresh : phase p.location = false
  reversed : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial
  arms : ∀ r,PathSite w hw v (armSpec w c.gate r)
  arm_location : ∀ r,(arms r).location = ((codes w v).get c.index).1
  walls : B.walls = (inventory w hw v).walls

namespace GatePhysicalContext

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} {c : CoreSite w hw v} {role : Fin 3}
  {p : PathSite w hw v (armSpec w c.gate role)} {B : Board (width w v) (height w v)}

/-- Construct every companion arm from the actual emitted source-cell record. -/
@[expose] def of_actual (hloc : p.location = ((codes w v).get c.index).1)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (ha : (inventory w hw v).Admissible)
    (g : Plan.VertexData) (hc : CellPlan.cell (v,p.location) = some (.inl (g,c.gate)))
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate role).target = !(armSpec w c.gate role).initial)
    (hB : B.walls = (inventory w hw v).walls) : GatePhysicalContext c role p B where
  location := hloc
  plane := hP
  typed := hT
  admissible := ha
  phase := phase
  fresh := fresh
  reversed := hb
  arms r := PathSite.arm p.location (g,c.gate) r (record_mem p.location (.inl (g,c.gate)) hc)
  arm_location _ := hloc
  walls := hB

/-- All real globally remaining identities at this selected core's execution phase. -/
@[expose] noncomputable def outside (C : GatePhysicalContext c role p B) : Finset (Cell (width w v) (height w v)) :=
  c.remaining (c.corePhase role p (tilePhases C.phase))

private def accessEnvironment (C : GatePhysicalContext c role p B) : c.AccessEnvironment where
  board := B
  walls := C.walls
  plane := C.plane
  typed := C.typed
  admissible := C.admissible
  Barm := C.arms 1
  Barm_location := C.arm_location 1

/-- Both actual exposed faces are joined for every mixed AND stock at this exact execution phase. -/
theorem andAccess (C : GatePhysicalContext c role p B) (hg : c.gate.core.isAND = true) (X : AndPhases w) :
    Access w true c.embedding B ((andMixedBoxes w X).map c.embedding.cells ∪ C.outside) :=
  c.and_mixed_access hg role p C.location C.accessEnvironment C.phase C.fresh C.reversed X

/-- Both actual exposed faces are joined for every mixed OR stock. -/
theorem orAccess (C : GatePhysicalContext c role p B) (hg : c.gate.core.isAND = false) (X : OrPhases w) :
    Access w false c.embedding B ((orMixedBoxes w X).map c.embedding.cells ∪ C.outside) :=
  c.or_mixed_access hg role p C.location C.accessEnvironment C.phase C.fresh C.reversed X

/-- Every AND local macro portal is reached through its actual A/B first-line crossings. -/
theorem andCanonicalAccess (C : GatePhysicalContext c role p B) (hg : c.gate.core.isAND = true) (X : AndPhases w) :
    AndAccess w c.embedding B ((andMixedBoxes w X).map c.embedding.cells ∪ C.outside) :=
  c.and_mixed_canonical_access hg role p C.location (C.arms 0) (C.arm_location 0)
    C.accessEnvironment C.phase C.fresh C.reversed X

end GatePhysicalContext
end PushPuzzle.PushS.FiniteSourceInventory

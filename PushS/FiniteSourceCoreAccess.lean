/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceCoreCrossings

/-! Literal actual mixed-stock access to every gate macro interface. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory.CoreSite

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry FiniteGateState FiniteGateTools
open FiniteGateMacros FiniteGateCore FiniteGateActiveRegion FiniteGateFaceGeometry FiniteGateOuterAccess
open FiniteGateFaceBridge FiniteGateCanonicalAccess
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height FiniteGeometry.side Line.width Line.height

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source} (c : CoreSite w hw v)

/-- The first actual primitive of every emitted gate arm has a genuine finite index. -/
private def firstArmIndex (role : Fin 3) : Fin (armSpec w c.gate role).segments.length :=
  ⟨0,by change 0 < (armRoute w c.gate role).length; rw [armRoute_length,route_length]; omega⟩

/-- The actual board and first-B-arm access data shared by every selected core phase. -/
structure AccessEnvironment where
  board : Board (width w v) (height w v)
  walls : board.walls = (inventory w hw v).walls
  plane : v.1.checkPlane = true
  typed : v.1.WellTyped [] []
  admissible : (inventory w hw v).Admissible
  Barm : PathSite w hw v (armSpec w c.gate 1)
  Barm_location : Barm.location = ((codes w v).get c.index).1

/-- The complete actual left/right access contract for every mixed AND stock. -/
theorem and_mixed_access (hg : c.gate.core.isAND = true) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (E : c.AccessEnvironment)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : AndPhases w) :
    Access w true c.embedding E.board ((andMixedBoxes w X).map c.embedding.cells ∪
      c.remaining (c.corePhase selected p (tilePhases phase))) := by
  have he (north : Bool) : c.embedding.cells (dock w true north) =
      (E.Barm.line (c.firstArmIndex 1)).actualEmbedding.cells (Line.outerCell w _ north (Line.outerHubX w _)) := by
    apply c.first_arm_anchor_eq 1 E.Barm E.Barm_location _ rfl _ north
    simpa [hg,PortAnnulus.innerDirection] using bDock_world w true north
  refine ⟨c.and_strip_frame hg selected p hloc E.admissible phase fresh hb X true E.board E.walls,
    c.and_strip_frame hg selected p hloc E.admissible phase fresh hb X false E.board E.walls,?_,?_⟩
  · simpa only [←he] using c.and_first_arm_faces hg 1 E.Barm E.Barm_location (c.firstArmIndex 1) rfl E.plane E.typed E.admissible _ X E.board E.walls true false
  · simpa only [←he] using c.and_first_arm_faces hg 1 E.Barm E.Barm_location (c.firstArmIndex 1) rfl E.plane E.typed E.admissible _ X E.board E.walls false true

/-- Every mixed OR stock has the same real first-B-line access. -/
theorem or_mixed_access (hg : c.gate.core.isAND = false) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (E : c.AccessEnvironment)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : OrPhases w) :
    Access w false c.embedding E.board ((orMixedBoxes w X).map c.embedding.cells ∪
      c.remaining (c.corePhase selected p (tilePhases phase))) := by
  have he (north : Bool) : c.embedding.cells (dock w false north) =
      (E.Barm.line (c.firstArmIndex 1)).actualEmbedding.cells (Line.outerCell w _ north (Line.outerHubX w _)) := by
    apply c.first_arm_anchor_eq 1 E.Barm E.Barm_location _ rfl _ north
    simpa [hg,PortAnnulus.innerDirection] using bDock_world w false north
  refine ⟨c.or_strip_frame hg selected p hloc E.admissible phase fresh hb X true E.board E.walls,
    c.or_strip_frame hg selected p hloc E.admissible phase fresh hb X false E.board E.walls,?_,?_⟩
  · simpa only [←he] using c.or_first_arm_faces hg 1 E.Barm E.Barm_location (c.firstArmIndex 1) rfl E.plane E.typed E.admissible _ X E.board E.walls true false
  · simpa only [←he] using c.or_first_arm_faces hg 1 E.Barm E.Barm_location (c.firstArmIndex 1) rfl E.plane E.typed E.admissible _ X E.board E.walls false true

/-- Both actual first-line crossings and all literal local corridors supply the full AND access. -/
theorem and_mixed_canonical_access (hg : c.gate.core.isAND = true) (selected : Fin 3)
    (p : PathSite w hw v (armSpec w c.gate selected)) (hloc : p.location = ((codes w v).get c.index).1)
    (pA : PathSite w hw v (armSpec w c.gate 0)) (hlocA : pA.location = ((codes w v).get c.index).1)
    (E : c.AccessEnvironment)
    (phase : GridRouting.Point → Bool) (fresh : phase p.location = false)
    (hb : (armSpec w c.gate selected).target = !(armSpec w c.gate selected).initial)
    (X : AndPhases w) :
    AndAccess w c.embedding E.board ((andMixedBoxes w X).map c.embedding.cells ∪
      c.remaining (c.corePhase selected p (tilePhases phase))) := by
  have hd : c.embedding.cells (node w true .aDock) =
      (pA.line (c.firstArmIndex 0)).actualEmbedding.cells (Line.outerCell w _ true (Line.outerHubX w _)) := by
    apply c.first_arm_anchor_eq 0 pA hlocA _ rfl _ true
    simpa [hg,PortAnnulus.innerDirection] using aDock_world w true
  have hb' : c.embedding.cells (node w true .aBridge) =
      (pA.line (c.firstArmIndex 0)).actualEmbedding.cells (Line.outerCell w _ false (Line.outerHubX w _)) := by
    apply c.first_arm_anchor_eq 0 pA hlocA _ rfl _ false
    simpa [hg,PortAnnulus.innerDirection] using aBridge_world w true
  refine ⟨c.and_mixed_access hg selected p hloc E phase fresh hb X,
    c.and_corridor_frame hg selected p hloc E.admissible phase fresh hb X .a E.board E.walls,
    c.and_corridor_frame hg selected p hloc E.admissible phase fresh hb X .aBridge E.board E.walls,?_,?_⟩
  · simpa only [←hd,←hb'] using c.and_first_arm_faces hg 0 pA hlocA (c.firstArmIndex 0) rfl E.plane E.typed E.admissible _ X E.board E.walls true false
  · simpa only [←hd,←hb'] using c.and_first_arm_faces hg 0 pA hlocA (c.firstArmIndex 0) rfl E.plane E.typed E.admissible _ X E.board E.walls false true

end PushPuzzle.PushS.FiniteSourceInventory.CoreSite

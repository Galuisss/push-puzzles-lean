/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceReadoutIndex
public import PushS.FiniteRoutingPortClaim
public import PushFS.Reduction.PortTriggerIndex
public import PushFS.Reduction.CanonicalPhases

/-! Actual thick-core outer-box thresholds read the original finite source configuration. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGateReadout
open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalInventory
open scoped Classical

attribute [local irreducible] codes width height Raster.width Raster.height InventoryAssembly.board InventoryAssembly.walls

variable (w : ℕ) (hw : 2 ≤ w) (v : CellPlan.Source)

private theorem CoreSite.boundarySignals_source (s : CoreSite w hw v)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) :
    s.boundarySignals hP hT (slotMatching w hw v hP hT).initialLabelled = s.gate.core.initial := by
  unfold CoreSite.boundarySignals
  split_ifs with hg
  · exact (s.andGlyph hg hP hT).boundarySignals_source
  · exact (s.orGlyph (Bool.eq_false_iff.mpr hg) hP hT).boundarySignals_source

private theorem CoreSite.boundarySignals_target (s : CoreSite w hw v)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v))
    (hs : S.position = (slotMatching w hw v hP hT).target) :
    s.boundarySignals hP hT S = s.gate.core.target := by
  unfold CoreSite.boundarySignals
  split_ifs with hg
  · exact (s.andGlyph hg hP hT).boundarySignals_target hs
  · exact (s.orGlyph (Bool.eq_false_iff.mpr hg) hP hT).boundarySignals_target hs

/-- The actual compiled core at the source record of a finite NCL incidence. -/
@[expose]
noncomputable def incidenceSite (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : PortIncidence (Word.compile v.1).graph) : CoreSite w hw v :=
  recordSite w hw v (sourceRecord v.1 hP hT i.1) (sourceRecord_mem v.1 hP hT i.1)

/-- The literal oriented high-slot threshold for one original NCL incidence. -/
@[expose]
noncomputable def sourceThreshold (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (i : PortIncidence (Word.compile v.1).graph) (p : Cell (width w v) (height w v)) : Bool :=
  let port := (incidenceSite w hw v hP hT i).port hP hT (sourceRole v.1 hvalid hP hT i)
  decide (PortHigh port.direction port.slot p)

/-- Read original finite NCL claims from the actual compiled physical labels. -/
@[expose]
noncomputable def sourceReadout (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed) :
    TriggerReadout (Fin (Word.compile v.1).edgeCount) (inventory w hw v).PhysicalLabel (width w v) (height w v) :=
  TriggerReadout.ofIncidences hG (sourcePortLabels w hw v hvalid hP hT hG) (sourceThreshold w hw v hvalid hP hT)

theorem sourceReadout_incidence (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v))
    (i : PortIncidence (Word.compile v.1).graph) :
    (sourceReadout w hw v hvalid hP hT hG).read S (incidentPort (Word.compile v.1).graph i) =
      gateClaim ((incidenceSite w hw v hP hT i).boundarySignals hP hT S) (sourceRole v.1 hvalid hP hT i) := by
  rw [sourceReadout,TriggerReadout.ofIncidences_read]
  change decide (PortHigh ((incidenceSite w hw v hP hT i).port hP hT (sourceRole v.1 hvalid hP hT i)).direction
      ((incidenceSite w hw v hP hT i).port hP hT (sourceRole v.1 hvalid hP hT i)).slot
      (S.position ((incidenceSite w hw v hP hT i).portLabel (sourceRole v.1 hvalid hP hT i)))) = _
  rw [←CoreSite.port_label (incidenceSite w hw v hP hT i) hP hT (sourceRole v.1 hvalid hP hT i)]
  exact ((incidenceSite w hw v hP hT i).port_claim hP hT S _).trans (portInflow_eq_gateClaim _ _)

theorem sourceReadout_initial (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed) :
    (sourceReadout w hw v hvalid hP hT hG).read (slotMatching w hw v hP hT).initialLabelled =
      PortClaims.full (fun e : Fin (Word.compile v.1).edgeCount => v.initialBits.getD e.val false) := by
  funext p
  obtain ⟨i,rfl⟩ := incidentPort_surjective hG p
  have hr := sourceReadout_incidence w hw v hvalid hP hT hG (slotMatching w hw v hP hT).initialLabelled i
  have hs := CoreSite.boundarySignals_source w hw v (incidenceSite w hw v hP hT i) hP hT
  refine hr.trans ((congrArg (fun bits => gateClaim bits (sourceRole v.1 hvalid hP hT i)) hs).trans ?_)
  change gateClaim (gateSignals ((sourceRecord v.1 hP hT i.1).ports,v.initialBits)) (sourceRole v.1 hvalid hP hT i) = _
  rw [gateSignals_claim,sourceRole_port]
  rfl

theorem sourceReadout_target (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v))
    (hs : S.position = (slotMatching w hw v hP hT).target) :
    (sourceReadout w hw v hvalid hP hT hG).read S =
      PortClaims.full (fun e : Fin (Word.compile v.1).edgeCount => v.targetBits.getD e.val false) := by
  funext p
  obtain ⟨i,rfl⟩ := incidentPort_surjective hG p
  rw [sourceReadout_incidence,CoreSite.boundarySignals_target w hw v _ hP hT S hs]
  change gateClaim (gateSignals ((sourceRecord v.1 hP hT i.1).ports,v.targetBits)) (sourceRole v.1 hvalid hP hT i) = _
  rw [gateSignals_claim,sourceRole_port]
  rfl

end PushPuzzle.PushS.FiniteSourceInventory

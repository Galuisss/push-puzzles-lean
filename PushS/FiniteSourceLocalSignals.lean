/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceReadoutSeams
public import PushS.FiniteSourceReadoutLegal

/-! Genuine source-cell neighbors relay or exclude the actual thick-core NCL claims. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open PushFS.Gadgets.Wires.Soundness

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

theorem outgoing_gate_readout_signal (c : CoreSite w hw v) (role : Fin 3) {a : Catalog.Bitmap.Args}
    (s : PathSite w hw v (armSpec w c.gate role)) (t : PathSite w hw v (wireSpec w a))
    (E : s.Endpoints) (F : t.Endpoints) (hin : c.gate.incoming.get role = false)
    (hloc : s.location = ((codes w v).get c.index).1) (hfirst : E.first = c.portLabel role)
    (hnext : F.first = ArmBoundary.outputIdentity s hin)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)) s.location = some t.location)
    (hd : Catalog.sourceDirection a.1 = PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role))
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hclaim : gateClaim (c.boundarySignals hP hT S) role = true) :
    (t.firstPort (wireSpec_geometry w a) F hP hT WireBoundary.length_pos).High S := by
  have hi := c.arm_claim_signal hP hT role s E hloc hfirst ArmBoundary.length_pos h
    ((portInflow_eq_gateClaim _ _).trans hclaim) ArmBoundary.lastIndex
  change (s.lastPort (armSpec_geometry w c.gate role) E hP hT ArmBoundary.length_pos).High S at hi
  exact gate_wire_readout_seam s t E F hin hnext hP hT hn hd ▸ hi

theorem incoming_gate_readout_exclusive (c : CoreSite w hw v) (role : Fin 3) {a : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (armSpec w c.gate role))
    (E : s.Endpoints) (F : t.Endpoints) (hin : c.gate.incoming.get role = true)
    (hloc : t.location = ((codes w v).get c.index).1) (hfirst : F.first = c.portLabel role)
    (hfinal : ∀ hk, F.final hk = WireBoundary.outputIdentity s)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (hn : neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) = (Catalog.targetDirection a.1).opposite)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final) :
    ¬(gateClaim (c.boundarySignals hP hT S) role = true ∧
      (s.lastPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S) := by
  rintro ⟨hclaim,hs⟩
  have hi := c.arm_claim_signal hP hT role t F hloc hfirst ArmBoundary.length_pos h
    ((portInflow_eq_gateClaim _ _).trans hclaim) ArmBoundary.lastIndex
  change (t.lastPort (armSpec_geometry w c.gate role) F hP hT ArmBoundary.length_pos).High S at hi
  exact wire_gate_ports_exclusive s t E F hin hfinal hP hT hn hd S ⟨hs,hi⟩

end PushPuzzle.PushS.FiniteSourceInventory

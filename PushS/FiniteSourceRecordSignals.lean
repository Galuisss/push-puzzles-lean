/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceLocalSignals
public import PushS.FiniteSourceWireInput

/-! Actual source records instantiate both gate-to-wire successful-path interfaces. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open PushFS.Gadgets.Wires.Soundness
open Cslib.Complexity.NCL Plan

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height InventoryAssembly.board InventoryAssembly.walls

theorem outgoing_record_readout (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g ∈ vertexRecords v.1) (role : Fin 3) (hout : (g.ports.port role).dir = false)
    {a : Catalog.Bitmap.Args} (e : ℕ) (t : PathSite w hw v (wireSpec w a))
    (hc : CellPlan.cell (v,t.location) = some (.inr (e,a)))
    (hn : neighbor (g.portDirection role) (refinePoint g.point) = some t.location)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final)
    (hclaim : gateClaim (observedSignals w hw v hP hT g hg S) role = true) :
    ∃ E : t.Endpoints, (t.firstPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S := by
  let c := recordSite w hw v g hg
  let s : PathSite w hw v (armSpec w c.gate role) :=
    PathSite.arm (hw := hw) (refinePoint g.point) (g,gateTileState (g,v.2)) role (record_entry v g hg)
  have hloc : s.location = ((codes w v).get c.index).1 := (recordSite_location w hw v g hg).symm
  have hi : c.gate.incoming.get role = false := (gateTileState_incoming g v.2.1 v.2.2 role).trans hout
  have hs : CellPlan.cell (v,s.location) = some (.inl (g,c.gate)) :=
    CellPlan.cell_gate v _ ((Raster.vertexAt_eq_some_iff _ _ _).mpr ⟨hg,rfl⟩)
  have hn' : neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role)) s.location = some t.location := hn
  let E := c.outgoingEndpoints role hi s hloc
  let F := actual_gate_wire_endpoints hP hT role hi g e s t hn' hs hc
  refine ⟨F,?_⟩
  exact outgoing_gate_readout_signal c role s t E F hi hloc rfl rfl hP hT hn'
    (gate_wire_direction hP hT role hi g e s t hn' hs hc) h hclaim

theorem incoming_record_readout_exclusive (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g ∈ vertexRecords v.1) (role : Fin 3) (hin : (g.ports.port role).dir = true)
    {a : Catalog.Bitmap.Args} (e : ℕ) (s : PathSite w hw v (wireSpec w a)) (E : s.Endpoints)
    (hc : CellPlan.cell (v,s.location) = some (.inr (e,a)))
    (hn : neighbor (Catalog.targetDirection a.1) s.location = some (refinePoint g.point))
    (hd : g.portDirection role = (Catalog.targetDirection a.1).opposite)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (h : Successful (slotMatching w hw v hP hT) S final) :
    ¬(gateClaim (observedSignals w hw v hP hT g hg S) role = true ∧
      (s.lastPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S) := by
  let c := recordSite w hw v g hg
  let t : PathSite w hw v (armSpec w c.gate role) :=
    PathSite.arm (hw := hw) (refinePoint g.point) (g,gateTileState (g,v.2)) role (record_entry v g hg)
  have hloc : t.location = ((codes w v).get c.index).1 := (recordSite_location w hw v g hg).symm
  have hi : c.gate.incoming.get role = true := (gateTileState_incoming g v.2.1 v.2.2 role).trans hin
  have ht : CellPlan.cell (v,t.location) = some (.inl (g,c.gate)) :=
    CellPlan.cell_gate v _ ((Raster.vertexAt_eq_some_iff _ _ _).mpr ⟨hg,rfl⟩)
  have hn' : neighbor (Catalog.targetDirection a.1) s.location = some t.location := hn
  have hd' : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) = (Catalog.targetDirection a.1).opposite := hd
  let F := actual_wire_gate_endpoints hP hT c role hi g e s t hloc hn' hd' ht hc
  exact incoming_gate_readout_exclusive c role s t E F hi hloc rfl (fun _ => rfl) hP hT hn' hd' h

end PushPuzzle.PushS.FiniteSourceInventory

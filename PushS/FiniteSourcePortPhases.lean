/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceSeparation
public import PushS.FiniteRoutingPortSpacing

/-! Actual source edge bits give complementary canonical phases on each reciprocal port. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires Plan
open Cslib.Complexity.NCL

private theorem portInflow_eq_gatePhase (g : GateTileState) (goal : Bool) (role : Fin 3) :
    portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role =
      PhysicalTiles.gatePhase g goal role := by
  cases goal <;> fin_cases role <;>
    simp [portInflow,coreSignals,PhysicalTiles.gatePhase,GateTileRouting.Inventory.initialPhase,
      GateTileRouting.Inventory.targetPhase,gateClaim,Gadgets.Gates.Signals.get]

theorem gate_wire_port_phase (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (vertex : VertexData) (g : GateTileState) (e : ℕ) (q : Catalog.Bitmap.Args)
    (hcg : CellPlan.cell (v,p) = some (.inl (vertex,g))) (hcw : CellPlan.cell (v,r) = some (.inr (e,q)))
    (role : Fin 3) (hd : PortAnnulus.outerDirection (g.pattern,g.rotation,role) = face) (goal : Bool) :
    portInflow (coreSignals g goal).left (coreSignals g goal).upper (coreSignals g goal).right role =
      if g.incoming.get role then !(PhysicalTiles.wirePhase q goal) else PhysicalTiles.wirePhase q goal := by
  obtain ⟨hvertex,hg⟩ := CellPlan.gate_sound hcg
  subst g
  obtain ⟨hmem,hp⟩ := Raster.vertexAt_sound hvertex
  have hd' : vertex.portDirection role = face := hd
  have hn' : PushFS.Reduction.neighbor (vertex.portDirection role) (refinePoint vertex.point) = some r := by
    rw [hd',hp]
    exact hn
  have he := (CellPlan.gate_adjacent v hP hT hmem role hn' hcw).1
  rw [portInflow_eq_gatePhase,gateTileState_incoming,PhysicalTiles.wire_phase hcw goal,←he]
  exact PhysicalTiles.gate_phase v vertex goal role

theorem wire_neighbor_phase (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (p r : GridRouting.Point) (face : Direction) (hn : PushFS.Reduction.neighbor face p = some r)
    (e f : ℕ) (a b : Catalog.Bitmap.Args)
    (hca : CellPlan.cell (v,p) = some (.inr (e,a))) (hcb : CellPlan.cell (v,r) = some (.inr (f,b)))
    (hu : CellPlan.Used (CellPlan.cell (v,p)) face) (goal : Bool) :
    PhysicalTiles.wirePhase a goal = PhysicalTiles.wirePhase b goal := by
  have he := (CellPlan.wire_adjacent v hP hT hn hca hcb hu).1
  rw [PhysicalTiles.wire_phase hca goal,PhysicalTiles.wire_phase hcb goal,he]

end PushPuzzle.PushS.FiniteSourceInventory

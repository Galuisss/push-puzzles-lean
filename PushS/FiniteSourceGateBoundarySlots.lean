/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceBoundarySlots

/-! Actual producing gate-arm and consuming gate-arm boundary identities. -/

@[expose] public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting FiniteGeometry Gadgets.Wires Plan
open Cslib.Complexity.NCL
open scoped Classical

attribute [local irreducible] codes width height inventory Line.width Line.height LineSite.atoms

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

namespace ArmBoundary

variable {g : GateTileState} {role : Fin 3} (s : PathSite w hw v (armSpec w g role))

theorem length_pos : 0 < (armSpec w g role).segments.length := by
  change 0 < (armRoute w g role).length
  rw [armRoute_length,route_length]
  omega

def lastIndex : Fin (armSpec w g role).segments.length := ⟨(armSpec w g role).segments.length-1,by
  have := length_pos (w := w) (g := g) (role := role)
  omega⟩

theorem lastIndex_final : (lastIndex (w := w) (g := g) (role := role)).val+1 = (armSpec w g role).segments.length := by
  have := length_pos (w := w) (g := g) (role := role)
  change (armSpec w g role).segments.length-1+1 = (armSpec w g role).segments.length
  omega

/-- The full arm ends at its literal boundary reference slot in every physical phase. -/
theorem last_coordinates (i : Fin (armSpec w g role).segments.length)
    (hi : i.val+1 = (armSpec w g role).segments.length) (phase : Bool) :
    coordinates ((s.line i).actualEmbedding.cells
      (Line.cell w hw (s.line i).atoms phase (Line.cutLastLabel w (s.line i).atoms))) =
      macroShift w s.location (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))
        (g.incoming.get role) phase) := by
  rw [(s.line i).actual_last_coordinates,s.line_location]
  have he : i.val = (armRoute w g role).length-1 := by
    change i.val+1 = (armRoute w g role).length at hi
    omega
  exact congrArg (macroShift w s.location) (by
    change ((armSpec w g role).line i.val).lastWorld w hw phase = _
    simpa only [he] using armSpec_last_slot w hw g role phase)

/-- A producing arm physically owns its last endpoint. -/
def outputIdentity (hin : g.incoming.get role = false) : (inventory w hw v).PhysicalLabel :=
  s.finalIdentity lastIndex lastIndex_final (by simp only [armSpec,hin,Bool.not_false])

theorem output_source (hin : g.incoming.get role = false) :
    coordinates ((inventory w hw v).source (outputIdentity s hin)) =
      macroShift w s.location (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))
        false (armSpec w g role).initial) := by
  unfold outputIdentity PathSite.finalIdentity
  rw [LineSite.source_finalLabel]
  have hh := s.line_initial lastIndex
  rw [hh,last_coordinates s _ lastIndex_final,hin]

theorem output_target (hin : g.incoming.get role = false) :
    coordinates ((inventory w hw v).target (outputIdentity s hin)) =
      macroShift w s.location (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role))
        false (armSpec w g role).target) := by
  unfold outputIdentity PathSite.finalIdentity
  rw [LineSite.target_finalLabel]
  have hh := s.line_target lastIndex
  rw [hh,last_coordinates s _ lastIndex_final,hin]

theorem output_owner_location (hin : g.incoming.get role = false) :
    ((codes w v).get (outputIdentity s hin).1).1 = s.location := by
  unfold outputIdentity
  rw [PathSite.finalIdentity_owner]
  exact s.line_location _

end ArmBoundary

/-- A producing gate's actual last arm identity supplies the following wire's whole first interface. -/
noncomputable def gate_wire_endpoints {g : GateTileState} (role : Fin 3) (hin : g.incoming.get role = false)
    {a : Catalog.Bitmap.Args} (s : PathSite w hw v (armSpec w g role)) (t : PathSite w hw v (wireSpec w a))
    (hn : PushFS.Reduction.neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) s.location = some t.location)
    (hd : Catalog.sourceDirection a.1 = PortAnnulus.outerDirection (g.pattern,g.rotation,role))
    (hs : (armSpec w g role).initial = a.2.1) (ht : (armSpec w g role).target = a.2.2) : t.Endpoints := by
  apply PathSite.Endpoints.of_kept t WireBoundary.keep_endpoint (ArmBoundary.outputIdentity s hin)
  · intro h
    apply boundaryCell_ext
    rw [ArmBoundary.output_source,WireBoundary.first_coordinates,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)).opposite true (!q))) hs)
  · intro h
    apply boundaryCell_ext
    rw [ArmBoundary.output_target,WireBoundary.first_coordinates,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (PortAnnulus.outerDirection (g.pattern,g.rotation,role)).opposite true (!q))) ht)

/-- The actual core and preceding wire give every real endpoint of a consuming gate arm. -/
noncomputable def wire_gate_endpoints (c : CoreSite w hw v) (role : Fin 3)
    (hin : c.gate.incoming.get role = true) {a : Catalog.Bitmap.Args}
    (s : PathSite w hw v (wireSpec w a)) (t : PathSite w hw v (armSpec w c.gate role))
    (hloc : t.location = ((codes w v).get c.index).1)
    (hn : PushFS.Reduction.neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) = (Catalog.targetDirection a.1).opposite)
    (hs : (armSpec w c.gate role).initial = !a.2.1)
    (ht : (armSpec w c.gate role).target = !a.2.2) : t.Endpoints where
  first := c.portLabel role
  final _ := WireBoundary.outputIdentity s
  source_first := c.arm_source_first role t hloc
  target_first := c.arm_target_first role t hloc
  source_final _ i hi := by
    apply boundaryCell_ext
    rw [WireBoundary.output_source,ArmBoundary.last_coordinates t i hi,hin,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (Catalog.targetDirection a.1).opposite true q)) hs.symm)
  target_final _ i hi := by
    apply boundaryCell_ext
    rw [WireBoundary.output_target,ArmBoundary.last_coordinates t i hi,hin,hd]
    exact (macro_boundary_phase _ _ _ _ hn).trans
      (congrArg (fun q => macroShift w t.location
        (boundarySlot w (Catalog.targetDirection a.1).opposite true q)) ht.symm)

/-- The actual reciprocal ordinary tile enters from a producing gate arm's source-grid face. -/
theorem gate_wire_direction (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    {g : GateTileState} (role : Fin 3) (hin : g.incoming.get role = false) {a : Catalog.Bitmap.Args}
    (vertex : VertexData) (e : ℕ) (s : PathSite w hw v (armSpec w g role)) (t : PathSite w hw v (wireSpec w a))
    (hn : PushFS.Reduction.neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) s.location = some t.location)
    (hcg : CellPlan.cell (v,s.location) = some (.inl (vertex,g)))
    (hcw : CellPlan.cell (v,t.location) = some (.inr (e,a))) :
    Catalog.sourceDirection a.1 = PortAnnulus.outerDirection (g.pattern,g.rotation,role) := by
  have hp : LocalPort (CellPlan.cell (v,s.location)) (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) false := by
    rw [hcg]
    exact ⟨role,rfl,hin⟩
  have hh := local_port_reciprocal v hP hT _ _ _ hn false hp
  rw [hcw] at hh
  rcases hh with ⟨_,hd⟩ | ⟨h,_⟩
  · have hd' := congrArg Direction.opposite hd
    simpa only [Direction.opposite_opposite] using hd'.symm
  · cases h

/-- Actual source and target edge bits supply both slot equalities of the producing gate/wire seam. -/
noncomputable def actual_gate_wire_endpoints (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    {g : GateTileState} (role : Fin 3) (hin : g.incoming.get role = false) {a : Catalog.Bitmap.Args}
    (vertex : VertexData) (e : ℕ) (s : PathSite w hw v (armSpec w g role)) (t : PathSite w hw v (wireSpec w a))
    (hn : PushFS.Reduction.neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) s.location = some t.location)
    (hcg : CellPlan.cell (v,s.location) = some (.inl (vertex,g)))
    (hcw : CellPlan.cell (v,t.location) = some (.inr (e,a))) : t.Endpoints := by
  have hs : (armSpec w g role).initial = a.2.1 := by
    simpa only [armSpec,coreSignals,Bool.false_eq_true,ite_false,hin,PhysicalTiles.wirePhase] using
      gate_wire_port_phase v hP hT _ _ _ hn vertex g e a hcg hcw role rfl false
  have ht : (armSpec w g role).target = a.2.2 := by
    simpa only [armSpec,coreSignals,ite_true,hin,Bool.false_eq_true,ite_false,PhysicalTiles.wirePhase] using
      gate_wire_port_phase v hP hT _ _ _ hn vertex g e a hcg hcw role rfl true
  exact gate_wire_endpoints role hin s t hn (gate_wire_direction hP hT role hin vertex e s t hn hcg hcw) hs ht

/-- Actual normal source phases determine both physical slot equalities at a consuming arm's wire seam. -/
noncomputable def actual_wire_gate_endpoints (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (c : CoreSite w hw v) (role : Fin 3) (hin : c.gate.incoming.get role = true) {a : Catalog.Bitmap.Args}
    (vertex : VertexData) (e : ℕ) (s : PathSite w hw v (wireSpec w a))
    (t : PathSite w hw v (armSpec w c.gate role))
    (hloc : t.location = ((codes w v).get c.index).1)
    (hn : PushFS.Reduction.neighbor (Catalog.targetDirection a.1) s.location = some t.location)
    (hd : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) = (Catalog.targetDirection a.1).opposite)
    (hcg : CellPlan.cell (v,t.location) = some (.inl (vertex,c.gate)))
    (hcw : CellPlan.cell (v,s.location) = some (.inr (e,a))) : t.Endpoints := by
  have hg : PushFS.Reduction.neighbor (PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role))
      t.location = some s.location := by rw [hd]; exact neighbor_reverse hn
  have hs : (armSpec w c.gate role).initial = !a.2.1 := by
    simpa only [armSpec,coreSignals,Bool.false_eq_true,ite_false,hin,ite_true,PhysicalTiles.wirePhase] using
      gate_wire_port_phase v hP hT _ _ _ hg vertex c.gate e a hcg hcw role rfl false
  have ht : (armSpec w c.gate role).target = !a.2.2 := by
    simpa only [armSpec,coreSignals,ite_true,hin,PhysicalTiles.wirePhase] using
      gate_wire_port_phase v hP hT _ _ _ hg vertex c.gate e a hcg hcw role rfl true
  exact wire_gate_endpoints c role hin s t hloc hn hd hs ht

end PushPuzzle.PushS.FiniteSourceInventory

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteRoutingConsumerLow
public import PushS.FiniteSourceEdgeWireForward
public import PushS.FiniteSourceTravelHulls

/-! The genuine source-edge frontier prepares the normal port immediately beyond every producer. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical

attribute [local irreducible] codes width height Raster.width Raster.height

private theorem frontier_next_wire_high (word : Word) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (pos other : GridRouting.Point)
    (H : TileFrontier word f e phase pos) (d : ℕ) (a : Catalog.Bitmap.Args)
    (hc : CellPlan.cell (oneEdgeSource word f e,other) = some (.inr (d,a)))
    (hs : UnitStep (Route.edgeSegments (refinedProgram word,e.val)) pos other) :
    PhysicalTiles.wirePhase a (phase other) = true := by
  obtain ⟨_,_,hi,ht⟩ := wire_reversed_phases word hP hT f e other d a hc hs.right_mem
  have hh := H.next other hs
  simpa only [PhysicalTiles.wirePhase,hi,ht,edgeWirePhase] using hh

theorem wire_successor_consumer_low (word : Word) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (pos other : GridRouting.Point)
    (H : TileFrontier word f e phase pos) (d : ℕ) (a : Catalog.Bitmap.Args)
    (hc : CellPlan.cell (oneEdgeSource word f e,pos) = some (.inr (d,a)))
    (hn : neighbor (Catalog.targetDirection a.1) pos = some other) :
    ConsumerLow (CellPlan.cell (oneEdgeSource word f e,other)) (Catalog.targetDirection a.1).opposite (phase other) := by
  let v := oneEdgeSource word f e
  obtain ⟨_,hk,hi,ht⟩ := wire_reversed_phases word hP hT f e pos d a hc H.point
  have hs : UnitStep (Route.edgeSegments (refinedProgram word,e.val)) pos other :=
    ⟨Catalog.targetDirection a.1,(Raster.outgoing_named _ _ _ _).mp (Raster.wireAt_target_arc hk),hn⟩
  have hhigh := H.next other hs
  have hwire : PhysicalTiles.wirePhase a (phase other) = true := by
    simpa only [PhysicalTiles.wirePhase,hi,ht,edgeWirePhase] using hhigh
  have hp : LocalPort (CellPlan.cell (v,pos)) (Catalog.targetDirection a.1) false := by
    rw [hc]
    exact Or.inr ⟨rfl,rfl⟩
  have hrec := local_port_reciprocal v hP hT pos other (Catalog.targetDirection a.1) hn false hp
  simp only [Bool.not_false] at hrec
  cases ho : CellPlan.cell (v,other) with
  | none => simp only [ho,LocalPort] at hrec
  | some code =>
    cases code with
    | inr b =>
      have hinput : (Catalog.targetDirection a.1).opposite = (Catalog.sourceDirection b.2.1).opposite := by
        rw [ho] at hrec
        rcases hrec with ⟨_,hd⟩ | ⟨hh,_⟩
        · exact hd
        · cases hh
      refine ⟨hinput,?_⟩
      exact frontier_next_wire_high word hP hT f e phase pos other H b.1 b.2 ho hs
    | inl g =>
      intro role hd
      have hin : g.2.incoming.get role = true :=
        local_port_unique (CellPlan.cell (v,other)) (Catalog.targetDirection a.1).opposite _ _
          (by rw [ho]; exact ⟨role,hd,rfl⟩) hrec
      refine ⟨hin,?_⟩
      have hh := gate_wire_port_phase v hP hT other pos (Catalog.targetDirection a.1).opposite
        (neighbor_reverse hn) g.1 g.2 d a ho hc role hd (phase other)
      simpa only [hin,ite_true,hwire,Bool.not_true] using hh

private theorem gate_producer_step (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (pos other : GridRouting.Point) (vertex : VertexData) (g : GateTileState)
    (hc : CellPlan.cell (v,pos) = some (.inl (vertex,g))) (role : Fin 3) (e : ℕ)
    (he : (vertex.ports.port role).edge = e) (hin : g.incoming.get role = false)
    (hn : neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) pos = some other) :
    UnitStep (Route.edgeSegments (refinedProgram v.1,e)) pos other := by
  obtain ⟨hv,hgate⟩ := CellPlan.gate_sound hc
  obtain ⟨hg,hpos⟩ := Raster.vertexAt_sound hv
  have hdir : (vertex.ports.port role).dir = false := by
    have hh : g.incoming.get role = (vertex.ports.port role).dir := by
      rw [hgate]
      exact gateTileState_incoming vertex _ _ role
    exact hh.symm.trans hin
  have hface : PortAnnulus.outerDirection (g.pattern,g.rotation,role) = vertex.portDirection role := by
    rw [hgate]
    rfl
  have ht := vertexRecord_tangent hP hT hg role
  dsimp only at ht
  rw [he,hdir] at ht
  simp only [Bool.false_eq_true,ite_false] at ht
  exact (show UnitStep (Route.edgeSegments (refinedProgram v.1,e)) pos other from
    ⟨vertex.portDirection role,by simpa only [hpos] using ht,by simpa only [hface] using hn⟩)

theorem gate_successor_consumer_low (word : Word) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (phase : GridRouting.Point → Bool) (pos other : GridRouting.Point)
    (H : TileFrontier word f e phase pos) (vertex : VertexData) (g : GateTileState)
    (hc : CellPlan.cell (oneEdgeSource word f e,pos) = some (.inl (vertex,g)))
    (role : Fin 3) (he : (vertex.ports.port role).edge = e.val) (hin : g.incoming.get role = false)
    (hn : neighbor (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) pos = some other) :
    ConsumerLow (CellPlan.cell (oneEdgeSource word f e,other))
      (PortAnnulus.outerDirection (g.pattern,g.rotation,role)).opposite (phase other) := by
  let v := oneEdgeSource word f e
  have hs := gate_producer_step v hP hT pos other vertex g hc role e.val he hin hn
  have hp : LocalPort (CellPlan.cell (v,pos)) (PortAnnulus.outerDirection (g.pattern,g.rotation,role)) false := by
    rw [hc]
    exact ⟨role,rfl,hin⟩
  have hrec := local_port_reciprocal v hP hT _ _ _ hn false hp
  simp only [Bool.not_false] at hrec
  cases ho : CellPlan.cell (v,other) with
  | none => simp only [ho,LocalPort] at hrec
  | some code =>
    cases code with
    | inl h => exact (neighboring_gates_impossible v pos other _ hn vertex h.1 g h.2 hc ho).elim
    | inr a =>
      rw [ho] at hrec
      rcases hrec with ⟨_,hd⟩ | ⟨hh,_⟩
      · exact ⟨hd,frontier_next_wire_high word hP hT f e phase pos other H a.1 a.2 ho hs⟩
      · cases hh

end PushPuzzle.PushS.FiniteSourceInventory

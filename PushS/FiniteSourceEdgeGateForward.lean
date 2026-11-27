/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceGateForward
public import PushS.FiniteSourceEdgeWireForward
public import PushS.FiniteRoutingPortClaim

/-! The genuine NCL source-edge frontier discharges every selected gate arm's dynamic preparation condition. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open Cslib.Complexity.NCL Plan SourceCanonical
open scoped Classical

attribute [local irreducible] codes width height inventory Raster.width Raster.height

/-- A routed gate arm and its unique actual source-cell record. -/
structure GateArmRecord {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    (core : CoreSite w hw v) (role : Fin 3) (path : PathSite w hw v (armSpec w core.gate role)) where
  location : path.location = ((codes w v).get core.index).1
  vertex : VertexData
  cell : CellPlan.cell (v,path.location) = some (.inl (vertex,core.gate))

theorem GateArmRecord.source_metadata {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}
    {c : CoreSite w hw v} {role : Fin 3} {p : PathSite w hw v (armSpec w c.gate role)}
    (R : GateArmRecord c role p) :
    R.vertex ∈ vertexRecords v.1 ∧ c.gate = gateTileState (R.vertex,v.2) := by
  obtain ⟨hv,hgate⟩ := CellPlan.gate_sound R.cell
  exact ⟨(Raster.vertexAt_sound hv).1,hgate⟩

/-- The selected actual gate arm has the edge's old physical inward phase and its exact complementary target. -/
theorem gate_reversed_phases (w : ℕ) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (g : VertexData) (hg : g ∈ vertexRecords word) (role : Fin 3) (he : (g.ports.port role).edge = e.val) :
    (armSpec w (gateTileState (g,(oneEdgeSource word f e).2)) role).initial =
      (if (g.ports.port role).dir then f e else !(f e)) ∧
    (armSpec w (gateTileState (g,(oneEdgeSource word f e).2)) role).target =
      !(armSpec w (gateTileState (g,(oneEdgeSource word f e).2)) role).initial := by
  constructor
  · change portInflow (gateSignals (g.ports,configBits f)).left (gateSignals (g.ports,configBits f)).upper
      (gateSignals (g.ports,configBits f)).right role = _
    rw [portInflow_eq_gateClaim,gateSignals_wire_phase,he,configBits_getD f e.val e.isLt]
  · change portInflow (gateSignals (g.ports,configBits (reverse f e))).left
      (gateSignals (g.ports,configBits (reverse f e))).upper (gateSignals (g.ports,configBits (reverse f e))).right role =
      !portInflow (gateSignals (g.ports,configBits f)).left (gateSignals (g.ports,configBits f)).upper
        (gateSignals (g.ports,configBits f)).right role
    rw [portInflow_eq_gateClaim,portInflow_eq_gateClaim]
    simpa only [he,ite_true] using gateClaim_reverse word hG hP hT f e g hg role

private theorem gate_predecessor_step (v : CellPlan.Source) (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (g : VertexData) (hg : g ∈ vertexRecords v.1) (role : Fin 3) (e : ℕ) (he : (g.ports.port role).edge = e)
    (hin : (g.ports.port role).dir = true) (q : GridRouting.Point)
    (hn : neighbor (g.portDirection role) (refinePoint g.point) = some q) :
    UnitStep (Route.edgeSegments (refinedProgram v.1,e)) q (refinePoint g.point) := by
  have ht := vertexRecord_tangent hP hT hg role
  dsimp only at ht
  rw [he,hin] at ht
  simp only [ite_true] at ht
  obtain ⟨q',hq,ha⟩ := ht
  have heq : q' = q := Option.some.inj (hq.symm.trans hn)
  rw [heq] at ha
  exact ⟨(g.portDirection role).opposite,ha,neighbor_reverse hn⟩

namespace ArmInput

/-- The genuine source-edge predecessor is precisely the actual ordinary endpoint owner held by a consuming arm. -/
private theorem frontier_outside {w : ℕ} {hw : 2 ≤ w} {word : Word}
    (hG : word.compile.Valid) (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    {f : Fin word.compile.edgeCount → Bool} {e : Fin word.compile.edgeCount}
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val) (I : ArmInput c role p)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location) :
    ∀ h,phase ((codes w (oneEdgeSource word f e)).get (I.endpoints.final h).1).1 = !(armSpec w c.gate role).initial := by
  let g := R.vertex
  have hc := R.cell
  obtain ⟨hv,hgate⟩ := CellPlan.gate_sound hc
  obtain ⟨hg,hpos⟩ := Raster.vertexAt_sound hv
  have hdir : c.gate.incoming.get role = (g.ports.port role).dir := by
    rw [hgate]
    exact gateTileState_incoming g _ _ role
  have hinit := (gate_reversed_phases w word hG hP hT f e g hg role he).1
  rw [←hgate] at hinit
  have hface : PortAnnulus.outerDirection (c.gate.pattern,c.gate.rotation,role) = g.portDirection role := by
    rw [hgate]
    rfl
  intro h
  have hin : c.gate.incoming.get role = true := by
    change Bool.not (c.gate.incoming.get role) = false at h
    cases hi : c.gate.incoming.get role <;> simp_all
  have hin' : (g.ports.port role).dir = true := hdir.symm.trans hin
  let q := ((codes w (oneEdgeSource word f e)).get (I.endpoints.final h).1).1
  have hn : neighbor (g.portDirection role) (refinePoint g.point) = some q := by
    rw [hpos,←hface]
    exact I.final_neighbor h
  have hstep := gate_predecessor_step (oneEdgeSource word f e) hP hT g hg role e.val he hin' q hn
  rw [hpos] at hstep
  have hp := H.previous q hstep
  unfold edgeWirePhase at hp
  have hflag : phase q = !(f e) := by
    cases hbit : f e <;> cases hq : phase q <;> simp_all
  have ha : (armSpec w c.gate role).initial = f e := by simpa only [hin',ite_true] using hinit
  exact hflag.trans (congrArg Bool.not ha.symm)

end ArmInput

/-- The unrelated real arms of this source gate may be marked complete after its selected core and arm execute. -/
private theorem actual_gate_idle (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (ha : (inventory w hw (oneEdgeSource word f e)).Admissible)
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val) :
    ∀ i : Fin (codes w (oneEdgeSource word f e)).length,
      ((codes w (oneEdgeSource word f e)).get i).1 = p.location → i ≠ c.index →
      ((codes w (oneEdgeSource word f e)).get i).2 ∉ (armSpec w c.gate role).codes →
      (((codes w (oneEdgeSource word f e)).get i).2).SamePhase := by
  obtain ⟨hg,hgate⟩ := R.source_metadata
  intro i hi hne hselected
  have hlocal := code_local w (oneEdgeSource word f e) ((codes w (oneEdgeSource word f e)).get i) (List.get_mem _ _)
  rw [hi,R.cell] at hlocal
  have hcore : ((codes w (oneEdgeSource word f e)).get i).2 ≠ .core c.gate := by
    intro hh
    apply hne
    apply code_get_injective ha
    exact Prod.ext (hi.trans R.location) (hh.trans c.code_eq.symm)
  apply gate_remaining_idle w word hG hP hT f e R.vertex hg role he
  · simpa only [hgate,localCodes,Option.elim_some,Sum.elim_inl] using hlocal
  · simpa only [hgate] using hcore
  · simpa only [hgate] using hselected

/-- Execute the actual selected gate tile of a genuine source-edge traversal; all dynamic arm and idle-stock conditions are discharged. -/
theorem edge_gate_tile_forward (w : ℕ) (hw : 2 ≤ w) (word : Word) (hG : word.compile.Valid)
    (hP : word.checkPlane = true) (hT : word.WellTyped [] [])
    (f : Fin word.compile.edgeCount → Bool) (e : Fin word.compile.edgeCount)
    (ha : (inventory w hw (oneEdgeSource word f e)).Admissible)
    (c : CoreSite w hw (oneEdgeSource word f e)) (role : Fin 3)
    (p : PathSite w hw (oneEdgeSource word f e) (armSpec w c.gate role))
    (R : GateArmRecord c role p) (he : (R.vertex.ports.port role).edge = e.val)
    (phase : GridRouting.Point → Bool) (H : TileFrontier word f e phase p.location)
    (B : Board (width w (oneEdgeSource word f e)) (height w (oneEdgeSource word f e)))
    (S : c.Action (c.corePhase role p (tilePhases phase)) B)
    (C : c.AnchorAccess (c.corePhase role p (tilePhases phase)) B (inventory w hw (oneEdgeSource word f e)).player)
    (F : ∀ cut,cut < PathSite.waveLength (P := armSpec w c.gate role) → ∀ a : PathEvent (armSpec w c.gate role),
      a.rank = PathSite.waveRank (P := armSpec w c.gate role) cut →
      p.EventFrame (armSpec_geometry w c.gate role) (actualArmInput hP hT c role p R.location R.vertex R.cell).endpoints B
        (p.wave (c.preparedArmBase role (tilePhases phase)) cut) a)
    (W : p.WaveAccess (armSpec_geometry w c.gate role) (c.preparedArmBase role (tilePhases phase)) B
      (inventory w hw (oneEdgeSource word f e)).player) :
    Reachable B (some 1) (profileState w hw (oneEdgeSource word f e) phase)
      (profileState w hw (oneEdgeSource word f e) (Function.update phase p.location true)) := by
  obtain ⟨hg,hgate⟩ := R.source_metadata
  have hb := (gate_reversed_phases w word hG hP hT f e R.vertex hg role he).2
  rw [←hgate] at hb
  exact c.gate_tile_forward role p R.location ha phase H.fresh
    (actual_gate_idle w hw word hG hP hT f e ha c role p R he)
    (actualArmInput hP hT c role p R.location R.vertex R.cell)
    ((actualArmInput hP hT c role p R.location R.vertex R.cell).frontier_outside hG hP hT c role p R he phase H)
    hb B S C F W

end PushPuzzle.PushS.FiniteSourceInventory

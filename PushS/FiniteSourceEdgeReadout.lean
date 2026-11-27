/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.FiniteSourceRecordSignals
public import PushFS.Reduction.PhysicalReadoutClaims
public import PushFS.Reduction.UnitPortPaths

/-! Complete actual source-edge paths exclude simultaneous claims at their two genuine core endpoints. -/

public section
namespace PushPuzzle.PushS.FiniteSourceInventory

open PushFS PushFS.Reduction FiniteRouting Gadgets.Wires
open PushFS.Gadgets.Wires.Soundness
open Cslib.Complexity.NCL PushPuzzle.NCL Plan

variable {w : ℕ} {hw : 2 ≤ w} {v : CellPlan.Source}

attribute [local irreducible] codes width height Raster.width Raster.height InventoryAssembly.board InventoryAssembly.walls

private def WireHigh (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v))
    (e : ℕ) (u : GridRouting.Point) : Prop :=
  ∃ (a : Catalog.Bitmap.Args) (p : PathSite w hw v (wireSpec w a)) (E : p.Endpoints),
    CellPlan.cell (v,p.location) = some (.inr (e,a)) ∧ p.location = u ∧
      (p.firstPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S

private theorem first_wire_high (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (e : Fin (Word.compile v.1).edgeCount) (g : VertexData) (hg : g ∈ vertexRecords v.1) (r : Fin 3)
    (he : (g.ports.port r).edge = e.val) (hout : (g.ports.port r).dir = false)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (hs : Successful (slotMatching w hw v hP hT) S final)
    (hclaim : gateClaim (observedSignals w hw v hP hT g hg S) r = true)
    {u : GridRouting.Point} (step : UnitStep (Route.edgeSegments (refinedProgram v.1,e.val)) (refinePoint g.point) u) :
    WireHigh (w := w) (hw := hw) hP hT S e.val u := by
  obtain ⟨d,ha,hn⟩ := step
  obtain ⟨r',hr',_,hd⟩ := vertexRecord_outgoing_role hP hT hg ha
  have hr : r' = r := vertexRecord_edges_injective hP hT hg (hr'.trans he.symm)
  subst r'
  rw [hd] at hn
  obtain ⟨p,k,hp,hcode,_,_,_⟩ := CellPlan.output_cell v hP hT hg r hout
  have hpu : p = u := Option.some.inj (hp.symm.trans hn)
  subst p
  rw [he] at hcode
  let a : Catalog.Bitmap.Args := (k,!(v.initialBits.getD e.val false),!(v.targetBits.getD e.val false))
  let t := PathSite.wire (hw := hw) u (e.val,a) (record_mem u (.inr (e.val,a)) hcode)
  obtain ⟨E,hhigh⟩ := outgoing_record_readout hP hT g hg r hout e.val t hcode hn hs hclaim
  exact ⟨a,t,E,hcode,rfl,hhigh⟩

section IncomingClaim
variable (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (e : Fin (Word.compile v.1).edgeCount) (g : VertexData) (hg : g ∈ vertexRecords v.1) (r : Fin 3)
    (he : (g.ports.port r).edge = e.val) (hin : (g.ports.port r).dir = true)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (hs : Successful (slotMatching w hw v hP hT) S final)
    (hclaim : gateClaim (observedSignals w hw v hP hT g hg S) r = true)
include hvalid hG hg he hin hs hclaim

private theorem gate_neighbor_blocked {a : Catalog.Bitmap.Args} (t : PathSite w hw v (wireSpec w a)) (E : t.Endpoints)
    (hc : CellPlan.cell (v,t.location) = some (.inr (e.val,a))) {u : GridRouting.Point}
    (hn : neighbor (Catalog.targetDirection a.1) t.location = some u) (b : VertexData) (role : Fin 3)
    (hv : Raster.vertexAt (v.1,u) = some b) (het : (b.ports.port role).edge = e.val)
    (hit : (b.ports.port role).dir = true) (hd : b.portDirection role = (Catalog.targetDirection a.1).opposite)
    (hhigh : (t.lastPort (wireSpec_geometry w a) E hP hT WireBoundary.length_pos).High S) : False := by
  obtain ⟨hb,hpoint⟩ := Raster.vertexAt_sound hv
  have hport : b.ports.port role = g.ports.port r :=
    congrArg₂ Port.mk (het.trans he.symm) (hit.trans hin.symm)
  have pair := PhysicalInventory.vertexRecord_port_unique v.1 hvalid hP hT hG b hb role g hg r hport
  have hbg : b = g := congrArg Prod.fst pair
  have hrole : role = r := congrArg Prod.snd pair
  subst b
  subst role
  have hneighbor : neighbor (Catalog.targetDirection a.1) t.location = some (refinePoint g.point) := by
    rw [hpoint]
    exact hn
  exact incoming_record_readout_exclusive hP hT g hg r hin e.val t E hc hneighbor hd hs ⟨hclaim,hhigh⟩

private theorem wire_high_next {u u' : GridRouting.Point} (hwire : WireHigh (w := w) (hw := hw) hP hT S e.val u)
    (step : UnitStep (Route.edgeSegments (refinedProgram v.1,e.val)) u u') :
    WireHigh (w := w) (hw := hw) hP hT S e.val u' := by
  obtain ⟨d,ha,hn⟩ := step
  obtain ⟨a,t,E,hcode,htu,hhigh⟩ := hwire
  subst u
  obtain ⟨_,_,hk,_,_⟩ := CellPlan.wire_sound hcode
  have hd : Catalog.targetDirection a.1 = d :=
    Raster.wireAt_outgoing_direction hk ((Raster.outgoing_named _ _ _ _).mpr ha)
  have htarget := t.ports_signal (wireSpec_geometry w a) E hP hT WireBoundary.length_pos hs hhigh
  obtain ⟨q,hq,alternatives⟩ := Raster.wire_target_neighbor hP hT hk
  have hqu : q = u' := Option.some.inj (hq.symm.trans (hd.symm ▸ hn))
  subst q
  rcases alternatives with ⟨k,hv,heq,hk',hflow⟩ | ⟨b,role,hv,het,hit,hdir⟩
  · have hcode' := CellPlan.of_wire v u' hv heq hk'
    let b : Catalog.Bitmap.Args := (k,!(v.initialBits.getD e.val false),!(v.targetBits.getD e.val false))
    let t' := PathSite.wire (hw := hw) u' (e.val,b) (record_mem u' (.inr (e.val,b)) hcode')
    have hn' : neighbor (Catalog.targetDirection a.1) t.location = some t'.location := hq
    let F := actual_wire_wire_endpoints hP hT e.val e.val t t' hn' hcode hcode'
    exact ⟨b,t',F,hcode',rfl,wire_wire_readout_signal t t' E F rfl hP hT hn' hflow hs hhigh⟩
  · exact False.elim (gate_neighbor_blocked hvalid hP hT hG e g hg r he hin hs hclaim
      t E hcode hq b role hv het hit hdir htarget)

end IncomingClaim

private theorem wire_high_not_gate (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] [])
    (S : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)) (e : ℕ)
    (g : VertexData) (hg : g ∈ vertexRecords v.1) :
    ¬WireHigh (w := w) (hw := hw) hP hT S e (refinePoint g.point) := by
  rintro ⟨a,t,E,hcode,hpoint,_⟩
  have hv : Raster.vertexAt (v.1,t.location) = some g := (Raster.vertexAt_eq_some_iff _ _ _).mpr ⟨hg,hpoint.symm⟩
  have hgate := CellPlan.cell_gate v t.location hv
  rw [hcode] at hgate
  cases hgate

/-- Every actual arbitrary successful trajectory respects each original source edge's two-end exclusivity. -/
theorem port_claims_exclusive (hvalid : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane = true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (e : Fin (Word.compile v.1).edgeCount)
    (g : VertexData) (hg : g ∈ vertexRecords v.1) (r : Fin 3)
    (he : (g.ports.port r).edge = e.val) (hout : (g.ports.port r).dir = false)
    (g' : VertexData) (hg' : g' ∈ vertexRecords v.1) (r' : Fin 3)
    (he' : (g'.ports.port r').edge = e.val) (hin : (g'.ports.port r').dir = true)
    {S final : LabelledState (inventory w hw v).PhysicalLabel (width w v) (height w v)}
    (hs : Successful (slotMatching w hw v hP hT) S final) :
    ¬(gateClaim (observedSignals w hw v hP hT g hg S) r = true ∧
      gateClaim (observedSignals w hw v hP hT g' hg' S) r' = true) := by
  intro both
  obtain ⟨path,hne⟩ := port_unitPath hP hT e g hg r he hout g' hg' r' he' hin
  let Ready (u : GridRouting.Point) := u = refinePoint g.point ∨ WireHigh (w := w) (hw := hw) hP hT S e.val u
  have initial : Ready (refinePoint g.point) := Or.inl rfl
  have next : ∀ u u', Ready u → UnitStep (Route.edgeSegments (refinedProgram v.1,e.val)) u u' → Ready u' := by
    intro u u' ready step
    rcases ready with hstart | hwire
    · subst u
      exact Or.inr (first_wire_high hP hT e g hg r he hout hs both.1 step)
    · exact Or.inr (wire_high_next hvalid hP hT hG e g' hg' r' he' hin hs both.2 hwire step)
  have traverse : ∀ {u}, UnitReach (Route.edgeSegments (refinedProgram v.1,e.val)) (refinePoint g.point) u → Ready u := by
    intro u hu
    induction hu with
    | refl => exact initial
    | tail _ step ih => exact next _ _ ih step
  rcases traverse path with heq | hwire
  · exact hne heq.symm
  · exact wire_high_not_gate hP hT S e.val g' hg' hwire

end PushPuzzle.PushS.FiniteSourceInventory

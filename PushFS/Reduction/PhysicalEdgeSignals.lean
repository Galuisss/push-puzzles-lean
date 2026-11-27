/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateWireSeams
public import PushFS.Reduction.PhysicalReadoutClaims
public import PushFS.Reduction.UnitPortPaths

/-! Literal successful-path signal propagation along every complete actual original source edge. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL Plan PhysicalBitmap Gadgets.Wires Catalog Soundness
set_option maxRecDepth 65536
set_option maxHeartbeats 200000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem wire_key {v : CellPlan.Source} {p : Raster.Cell v.1} {e : ℕ} {a : Catalog.Bitmap.Args}
    (hc : CellPlan.cell (v,(p.1.val,p.2.val))=some (.inr (e,a))) :
    PhysicalTiles.key (CellPlan.cell (v,(p.1.val,p.2.val)))=some (.inr a) := by rw [hc]; rfl

private def WireHigh (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (e : ℕ) (u : GridRouting.Point) : Prop :=
  ∃(p : Raster.Cell v.1) (a : Catalog.Bitmap.Args),∃hc : CellPlan.cell (v,(p.1.val,p.2.val))=some (.inr (e,a)),
    (p.1.val,p.2.val)=u ∧
    let image:=tileImage v hP hT (wireIndex v p a (wire_key hc))
    Catalog.sourceHigh a.1 image.dx image.dy (S.position (image.labels (firstLabel a.1)))

/-- The two actual inward gate observations of one original numbered source edge are exclusive. -/
theorem port_claims_exclusive (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (e : Fin (Word.compile v.1).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3)
    (he : (g.ports.port r).edge=e.val) (hout : (g.ports.port r).dir=false)
    (h : VertexData) (hh : h∈vertexRecords v.1) (s : Fin 3)
    (he' : (h.ports.port s).edge=e.val) (hin : (h.ports.port s).dir=true)
    {S T : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S T) :
    ¬(gateClaim (observedSignals v g hg S) r=true ∧gateClaim (observedSignals v h hh S) s=true) := by
  intro both
  have gh:=observed_to_outer v hP hT g hg hs r both.1
  have hhig:=observed_to_outer v hP hT h hh hs s both.2
  obtain ⟨path,hne⟩:=port_unitPath hP hT e g hg r he hout h hh s he' hin
  let Ready (u : GridRouting.Point):=u=refinePoint g.point ∨WireHigh v hP hT S e.val u
  have initial : Ready (refinePoint g.point):=Or.inl rfl
  have next : ∀u u',Ready u→UnitStep (Route.edgeSegments (refinedProgram v.1,e.val)) u u'→Ready u' := by
    intro u u' ready step
    obtain ⟨d,ha,hn⟩:=step
    rcases ready with hstart|hwire
    · subst u
      obtain ⟨r',hr',_,hd⟩:=vertexRecord_outgoing_role hP hT hg ha
      have hr:r'=r:=vertexRecord_edges_injective hP hT hg (hr'.trans he.symm)
      subst r'
      rw [hd] at hn
      obtain ⟨p,k,hp,hcode,_,_,_⟩:=CellPlan.output_cell v hP hT hg r hout
      have hpu:p=u':=Option.some.inj (hp.symm.trans hn)
      subst p
      rw [he] at hcode
      have hb:=CellPlan.nonempty_bounds (show CellPlan.cell (v,u')≠none by rw [hcode]; simp)
      let q : Raster.Cell v.1:=(⟨u'.1,hb.1⟩,⟨u'.2,hb.2⟩)
      let a : Catalog.Bitmap.Args:=(k,!(v.2.1.getD e.val false),!(v.2.2.getD e.val false))
      have hc : CellPlan.cell (v,(q.1.val,q.2.val))=some (.inr (e.val,a)):=hcode
      exact Or.inr ⟨q,a,hc,rfl,outgoing_gate_signal v hP hT g hg r q a (wire_key hc) hn hout hs gh⟩
    · obtain ⟨p,a,hcode,hpu,hhigh⟩:=hwire
      subst u
      obtain ⟨_,_,hk,_,_⟩:=CellPlan.wire_sound hcode
      have hd : targetDirection a.1=d:=Raster.wireAt_outgoing_direction hk ((Raster.outgoing_named _ _ _ _).mpr ha)
      have htarget:=wire_signal v hP hT p a (wire_key hcode) hs (certificate v hP hT) (matching_ordered v hP hT) hhigh
      obtain ⟨q,hq,alternatives⟩:=Raster.wire_target_neighbor hP hT hk
      have hqu:q=u':=Option.some.inj (hq.symm.trans (hd.symm ▸hn))
      subst q
      rcases alternatives with ⟨k,hv,heq,hk',hflow⟩|⟨b,t,hv,het,hit,hdir⟩
      · have hcode':=CellPlan.of_wire v u' hv heq hk'
        have hb:=CellPlan.nonempty_bounds (show CellPlan.cell (v,u')≠none by rw [hcode']; simp)
        let q : Raster.Cell v.1:=(⟨u'.1,hb.1⟩,⟨u'.2,hb.2⟩)
        let b : Catalog.Bitmap.Args:=(k,!(v.2.1.getD e.val false),!(v.2.2.getD e.val false))
        have hc : CellPlan.cell (v,(q.1.val,q.2.val))=some (.inr (e.val,b)):=hcode'
        exact Or.inr ⟨q,b,hc,rfl,wire_seam_signal v hP hT p q a b (wire_key hcode) (wire_key hc)
          hq hflow hs (certificate v hP hT) htarget⟩
      · obtain ⟨hb,hpoint⟩:=Raster.vertexAt_sound hv
        have hport : b.ports.port t=h.ports.port s:=
          congrArg₂ Port.mk (het.trans he'.symm) (hit.trans hin.symm)
        have pair:=vertexRecord_port_unique v.1 hw hP hT hG b hb t h hh s hport
        have hbh:b=h:=congrArg Prod.fst pair
        have hts:t=s:=congrArg Prod.snd pair
        subst b
        subst t
        have hneighbor : neighbor (h.portDirection s) (refinePoint h.point)=some (p.1.val,p.2.val):=by
          rw [hdir,hpoint]
          exact neighbor_reverse hq
        exact False.elim (incoming_gate_exclusive v hP hT h hh s p a (wire_key hcode) hneighbor hin hs hhig htarget)
  have traverse : ∀{u},UnitReach (Route.edgeSegments (refinedProgram v.1,e.val)) (refinePoint g.point) u→Ready u := by
    intro u hu
    induction hu with
    | refl=>exact initial
    | tail _ step ih=>exact next _ _ ih step
  have finalReady : Ready (refinePoint h.point):=traverse path
  rcases finalReady with heq|hw'
  · exact hne heq.symm
  · obtain ⟨p,a,hcode,hpu,_⟩:=hw'
    have hv : Raster.vertexAt (v.1,(p.1.val,p.2.val))=some h:=
      (Raster.vertexAt_eq_some_iff _ _ _).mpr ⟨hh,hpu.symm⟩
    have hgate:=CellPlan.cell_gate v (p.1.val,p.2.val) hv
    rw [hcode] at hgate
    cases hgate
end PushPuzzle.PushFS.Reduction.PhysicalInventory

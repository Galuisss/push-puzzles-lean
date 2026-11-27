/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalTriggerReadout
public import PushFS.Reduction.GateClaims
public import PushFS.Gadgets.Gates.Soundness.Relay
import Mathlib.Data.List.GetD

/-! Literal placed gate glyphs and the original finite source's inward observations. -/

public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalBitmap Gadgets
open Gates.Soundness Wires.Soundness
attribute [local irreducible] Raster.width Raster.height

theorem core_fits (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) :
    (coreOffset g).1+81≤strideX*Raster.width v.1+7 ∧
      (coreOffset g).2+107≤strideY*Raster.height v.1+7 := by
  have hc:=core_coordinates v g hg (80,106)
  have hx:=((coreEmbedding v g hg).cells (80,106)).1.isLt
  have hy:=((coreEmbedding v g hg).cells (80,106)).2.isLt
  have hcx:=congrArg Prod.fst hc
  have hcy:=congrArg Prod.snd hc
  dsimp only at hcx hcy
  omega

theorem core_cells (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1) (p : Gates.C) :
    (coreEmbedding v g hg).cells p=
      (GridEmbedding.translate (coreOffset g).1 (coreOffset g).2
        (core_fits v g hg).1 (core_fits v g hg).2).cells p := by
  have h:=core_coordinates v g hg p
  apply Prod.ext <;> apply Fin.ext
  · exact congrArg Prod.fst h
  · exact congrArg Prod.snd h

/-- Exact axis names required by the central long-wall gate's soundness proof. -/
structure CoreTags (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1) : Prop where
  source : ∀l,A.name ((coreEmbedding v g hg).cells
      (Gates.position g.ports.isAND (gateSignals (g.ports,(PhysicalTiles.bits v false))) l))=
    AxisTrack.shift (coreOffset g).1 (coreOffset g).2
      (Gates.axisName g.ports.isAND (Gates.position g.ports.isAND (gateSignals (g.ports,(PhysicalTiles.bits v false))) l))
  junction : A.name ((coreEmbedding v g hg).cells (junctionPoint g.ports.isAND))=
    .horizontal ((coreOffset g).2+90)
  protectedTag : g.ports.isAND=true→A.name ((coreEmbedding v g hg).cells (39,90))=
    .sink ((coreOffset g).1+39) ((coreOffset g).2+90)

/-- The actual central core, with every real physical box and its exact whole-board placement. -/
@[expose] noncomputable def coreGlyph (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1)
    (tags : CoreTags v hP hT A g hg) :
    GateGlyph (rawSlotMatching v hP hT) A g.ports.isAND where
  dx:=(coreOffset g).1
  dy:=(coreOffset g).2
  fit_x:=(core_fits v g hg).1
  fit_y:=(core_fits v g hg).2
  initialSignals:=gateSignals (g.ports,(PhysicalTiles.bits v false))
  targetSignals:=gateSignals (g.ports,(PhysicalTiles.bits v true))
  labels:=coreLabels v g hg
  walls p:=by
    change (GridEmbedding.translate (coreOffset g).1 (coreOffset g).2 (core_fits v g hg).1 (core_fits v g hg).2).cells p∈(atlas v hP hT).board.walls ↔_
    rw [←core_cells]
    exact core_walls_agree v hP hT g hg p
  sources l:=(coreLabel_source v hP hT g hg l).trans (core_cells v g hg _)
  targets l:=(coreLabel_target v hP hT g hg l).trans (core_cells v g hg _)
  tracks l:=by
    change A.name ((rawSlotMatching v hP hT).source (coreLabel v g hg l))=_
    rw [coreLabel_source]
    exact tags.source l
  junctionTag:=by
    change A.name ((GridEmbedding.translate (coreOffset g).1 (coreOffset g).2 (core_fits v g hg).1 (core_fits v g hg).2).cells (junctionPoint g.ports.isAND))=_
    rw [←core_cells]
    exact tags.junction
  protectedTag h:=by
    change A.name ((GridEmbedding.translate (coreOffset g).1 (coreOffset g).2 (core_fits v g hg).1 (core_fits v g hg).2).cells (39,90))=_
    rw [←core_cells]
    exact tags.protectedTag h

/-- Inward threshold observations at the three actual core triggers. -/
@[expose] noncomputable def observedSignals (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) : Gates.Signals :=
  ⟨gateThreshold g 0 (S.position (coreLabel v g hg (triggerIndex g.ports.isAND 0))),
    gateThreshold g 1 (S.position (coreLabel v g hg (triggerIndex g.ports.isAND 1))),
    !(gateThreshold g 2 (S.position (coreLabel v g hg (triggerIndex g.ports.isAND 2))))⟩

private theorem observedSignals_claim (v : CellPlan.Source) (g : VertexData) (hg : g∈vertexRecords v.1)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (r : Fin 3) : gateClaim (observedSignals v g hg S) r=
      gateThreshold g r (S.position (coreLabel v g hg (triggerIndex g.ports.isAND r))) := by
  fin_cases r <;> simp [gateClaim,observedSignals,Gates.Signals.get]

theorem coreGlyph_decode (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1)
    (tags : CoreTags v hP hT A g hg)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)) :
    (coreGlyph v hP hT A g hg tags).decode S=observedSignals v g hg S := by
  unfold GateGlyph.decode
  dsimp only [coreGlyph,GateGlyph.a,GateGlyph.b,GateGlyph.c,coreLabels]
  by_cases hk:g.ports.isAND=true <;>
    simp [observedSignals,gateThreshold,thresholdAt,triggerIndex,hk]
  all_goals first | exact ⟨rfl,rfl⟩ | rfl

/-- Every intermediate state of a successful actual whole-board path satisfies each actual gate. -/
private theorem observedSignals_legal (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (A : AxisTracks (puzzle v hP hT)) (g : VertexData) (hg : g∈vertexRecords v.1)
    (tags : CoreTags v hP hT A g hg) (cert : Certificate (puzzle v hP hT))
    (ordered : (rawSlotMatching v hP hT).Ordered)
    (ha : (Word.compile v.1).checkLegal (PhysicalTiles.bits v false)=true) (hb : (Word.compile v.1).checkLegal (PhysicalTiles.bits v true)=true)
    {S final : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S final) :
    Gates.legal g.ports.isAND (observedSignals v g hg S) := by
  rw [←coreGlyph_decode v hP hT A g hg tags S]
  exact (coreGlyph v hP hT A g hg tags).decode_legal hs cert ordered
    (record_legal v.1 hw hP hT (PhysicalTiles.bits v false) ha g hg) (record_legal v.1 hw hP hT (PhysicalTiles.bits v true) hb g hg)

theorem sourceReadout_incidence (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (i : PortIncidence (Word.compile v.1).graph) :
    (sourceReadout v hw hP hT hG).read S (incidentPort (Word.compile v.1).graph i)=
      gateClaim (observedSignals v (sourceRecord v.1 hP hT i.1) (sourceRecord_mem v.1 hP hT i.1) S)
        (sourceRole v.1 hw hP hT i) := by
  rw [observedSignals_claim]
  exact TriggerReadout.ofIncidences_read hG (sourceTriggers v hw hP hT hG)
    (fun i=>gateThreshold (sourceRecord v.1 hP hT i.1) (sourceRole v.1 hw hP hT i)) S i

theorem sourceRole_surjective (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) :
    Function.Surjective (fun j : Fin ((Word.compile w).graph i).ports.length=>
      sourceRole w hw hP hT ⟨i,j⟩) := by
  have hinj : Function.Injective (fun j : Fin ((Word.compile w).graph i).ports.length=>
      sourceRole w hw hP hT ⟨i,j⟩) := by
    intro j k he
    have hh : (⟨i,j⟩ : PortIncidence (Word.compile w).graph)=⟨i,k⟩ :=
      source_role_injective w hw hP hT hw.2.2 (show (sourceRecord w hP hT i,sourceRole w hw hP hT ⟨i,j⟩)=
        (sourceRecord w hP hT i,sourceRole w hw hP hT ⟨i,k⟩) from Prod.ext rfl he)
    exact eq_of_heq (Sigma.mk.inj hh).2
  have hmap:=congrFun ((Word.compile w).graph_map_val hw.1) i
  have hlen:=congrArg (fun u : Vertex ℕ=>u.ports.length) hmap
  simp only [ConstraintGraph.map,Vertex.map,List.length_map] at hlen
  have hports:=(sourceRecord_ports w hw hP hT i).length_eq
  have hthree : (sourceRecord w hP hT i).ports.vertex.ports.length=3 := by
    unfold OrderedPorts.vertex
    split <;> rfl
  have hcard : Fintype.card (Fin ((Word.compile w).graph i).ports.length)=Fintype.card (Fin 3) := by
    simp only [Fintype.card_fin]
    exact hlen.trans (hports.trans hthree)
  exact ((Fintype.bijective_iff_injective_and_card _).mpr ⟨hinj,hcard⟩).2

private def extendedClaims {n : ℕ} (c : PortClaims.Claims (Fin n)) : PortClaims.Claims ℕ :=
  fun p=>if h:p.edge<n then c ⟨⟨p.edge,h⟩,p.dir⟩ else false

private theorem extendedClaims_pullback {n : ℕ} (c : PortClaims.Claims (Fin n)) :
    PortClaims.pullback Fin.val (extendedClaims c)=c := by
  funext ⟨e,d⟩
  change (if h:e.val<n then c ⟨⟨e.val,h⟩,d⟩ else false)=c ⟨e,d⟩
  rw [dite_eq_left e.isLt]

private theorem record_claim_role (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : PortClaims.Claims (Fin (Word.compile w).edgeCount))
    (signals : ∀g : VertexData,g∈vertexRecords w→Gates.Signals)
    (hread : ∀i : PortIncidence (Word.compile w).graph,c (incidentPort (Word.compile w).graph i)=
      gateClaim (signals (sourceRecord w hP hT i.1) (sourceRecord_mem w hP hT i.1)) (sourceRole w hw hP hT i))
    (i : Fin (Word.compile w).vertices.length) (r : Fin 3) :
    extendedClaims c ((sourceRecord w hP hT i).ports.port r)=
      gateClaim (signals (sourceRecord w hP hT i) (sourceRecord_mem w hP hT i)) r := by
  obtain ⟨j,rfl⟩:=sourceRole_surjective w hw hP hT i r
  rw [sourceRole_port w hw hP hT ⟨i,j⟩]
  exact (congrFun (extendedClaims_pullback c) (incidentPort (Word.compile w).graph ⟨i,j⟩)).trans (hread ⟨i,j⟩)

/-- Legal threshold signals on the actual source records satisfy every finite NCL vertex. -/
theorem record_claims_legal (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : PortClaims.Claims (Fin (Word.compile w).edgeCount))
    (signals : ∀g : VertexData,g∈vertexRecords w→Gates.Signals)
    (hread : ∀i : PortIncidence (Word.compile w).graph,c (incidentPort (Word.compile w).graph i)=
      gateClaim (signals (sourceRecord w hP hT i.1) (sourceRecord_mem w hP hT i.1)) (sourceRole w hw hP hT i))
    (hlocal : ∀g (hg : g∈vertexRecords w),Gates.legal g.ports.isAND (signals g hg)) :
    PortClaims.Legal (Word.compile w).graph c := by
  let c':=extendedClaims c
  apply (congrArg (PortClaims.Legal (Word.compile w).graph) (extendedClaims_pullback c)).mp
  apply (graph_claims_legal_iff (Word.compile w) hw.1 c').mpr
  intro u hu
  obtain ⟨i,rfl⟩:=List.get_of_mem hu
  let g:=sourceRecord w hP hT i
  have hg:=sourceRecord_mem w hP hT i
  have hroles:=record_claim_role w hw hP hT c signals hread i
  have hsignals : g.ports.claimSignals c'=signals g hg := by
    change Gates.Signals.mk _ _ _=Gates.Signals.mk _ _ _
    congr 1
    · exact hroles 0
    · exact hroles 1
    · have hr:=hroles 2
      change c' g.ports.output=(!(signals g hg).right) at hr
      change (!(c' g.ports.output))=(signals g hg).right
      rw [hr,Bool.not_not]
  have hl:PortClaims.Satisfied g.ports.vertex c' :=
    (legal_claimSignals_iff g.ports c').mp (hsignals.symm ▸hlocal g hg)
  have hmin : ((Word.compile w).vertices.get i).minInflow=g.ports.vertex.minInflow := by
    have hm : ((Word.compile w).graph i).minInflow=2 := by
      rcases hw.2.1 i with ⟨_,_,_,hm,_⟩|⟨_,_,_,hm,_⟩ <;> exact hm
    change ((Word.compile w).graph i).minInflow=_
    rw [hm]
    unfold OrderedPorts.vertex
    split <;> rfl
  exact (PortClaims.satisfied_iff_of_perm (sourceRecord_ports w hw hP hT i) hmin c').mpr hl

/-- Legal actual threshold triples imply every original finite weighted vertex constraint. -/
private theorem sourceReadout_legal_of_gates (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hlocal : ∀g (hg : g∈vertexRecords v.1),Gates.legal g.ports.isAND (observedSignals v g hg S)) :
    PortClaims.Legal (Word.compile v.1).graph ((sourceReadout v hw hP hT hG).read S) :=
  record_claims_legal v.1 hw hP hT ((sourceReadout v hw hP hT hG).read S)
    (fun g hg=>observedSignals v g hg S) (sourceReadout_incidence v hw hP hT hG S) hlocal

/-- On every successful physical split, the exact original finite readout obeys all vertex constraints. -/
theorem sourceReadout_legal (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (A : AxisTracks (puzzle v hP hT))
    (tags : ∀g (hg : g∈vertexRecords v.1),CoreTags v hP hT A g hg)
    (cert : Certificate (puzzle v hP hT)) (ordered : (rawSlotMatching v hP hT).Ordered)
    (ha : (Word.compile v.1).checkLegal (PhysicalTiles.bits v false)=true) (hb : (Word.compile v.1).checkLegal (PhysicalTiles.bits v true)=true)
    {S final : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7)}
    (hs : Successful (rawSlotMatching v hP hT) S final) :
    PortClaims.Legal (Word.compile v.1).graph ((sourceReadout v hw hP hT hG).read S) :=
  sourceReadout_legal_of_gates v hw hP hT hG S
    (fun g hg=>observedSignals_legal v hw hP hT A g hg (tags g hg) cert ordered ha hb hs)

end PushPuzzle.PushFS.Reduction.PhysicalInventory

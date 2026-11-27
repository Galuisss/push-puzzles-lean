/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalGateReadout

/-! Every original finite readout claim is exactly the observed role of any matching actual source record. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory

open Cslib.Complexity.NCL PushPuzzle.NCL Plan PhysicalBitmap Gadgets
set_option maxRecDepth 65536
set_option maxHeartbeats 100000
attribute [local irreducible] Raster.width Raster.height StorageAtlas.initial StorageAtlas.board

private theorem sourceRecord_eq (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) {g : VertexData} (hg : g∈vertexRecords w)
    (hi : g.index=i.val) : sourceRecord w hP hT i=g := by
  have hn : ((vertexRecords w).map VertexData.index).Nodup:=by
    rw [vertexRecords_indices hP hT]
    exact List.nodup_range
  exact List.inj_on_of_nodup_map hn (sourceRecord_mem w hP hT i) hg ((sourceRecord_index w hP hT i).trans hi.symm)

/-- Every actual placed role is the unique geometric realization of an original finite incidence. -/
private theorem sourceRecord_role_exists (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3) :
    ∃i : PortIncidence (Word.compile w).graph,
      (sourceRecord w hP hT i.1,sourceRole w hw hP hT i)=(g,r) := by
  have hb: g.index<(Word.compile w).vertices.length:=(vertexRecord_correct hw hP hT hg).1
  let i : Fin (Word.compile w).vertices.length:=⟨g.index,hb⟩
  obtain ⟨j,hj⟩:=sourceRole_surjective w hw hP hT i r
  exact ⟨⟨i,j⟩,Prod.ext (sourceRecord_eq w hP hT i hg rfl) hj⟩

theorem vertexRecord_edge_lt (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3) :
    (g.ports.port r).edge<(Word.compile w).edgeCount := by
  obtain ⟨i,hi⟩:=sourceRecord_role_exists w hw hP hT g hg r
  have hp : (incidentPort (Word.compile w).graph i).map Fin.val=g.ports.port r :=
    (sourceRole_port w hw hP hT i).symm.trans (congrArg (fun q : VertexData×Fin 3=>q.1.ports.port q.2) hi)
  exact (congrArg Port.edge hp) ▸(incidentPort (Word.compile w).graph i).edge.isLt

/-- Equal original numbered ports select the same complete placed source record and physical role. -/
theorem vertexRecord_port_unique (w : Word) (hw : (Word.compile w).Valid)
    (hP : w.checkPlane=true) (hT : w.WellTyped [] []) (hG : (Word.compile w).graph.WellFormed)
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3)
    (h : VertexData) (hh : h∈vertexRecords w) (s : Fin 3)
    (hp : g.ports.port r=h.ports.port s) : (g,r)=(h,s) := by
  obtain ⟨i,hi⟩:=sourceRecord_role_exists w hw hP hT g hg r
  obtain ⟨j,hj⟩:=sourceRecord_role_exists w hw hP hT h hh s
  have hpi: (incidentPort (Word.compile w).graph i).map Fin.val=g.ports.port r := by
    have he:=sourceRole_port w hw hP hT i
    exact he.symm.trans (congrArg (fun q : VertexData×Fin 3=>q.1.ports.port q.2) hi)
  have hpj: (incidentPort (Word.compile w).graph j).map Fin.val=h.ports.port s := by
    have he:=sourceRole_port w hw hP hT j
    exact he.symm.trans (congrArg (fun q : VertexData×Fin 3=>q.1.ports.port q.2) hj)
  have hij : i=j:=(incidentPort_bijective hG).1 (port_map_val_injective _ (hpi.trans (hp.trans hpj.symm)))
  exact hi.symm.trans (hij ▸hj)

/-- The two actual gate-role observations suffice for the exact finite original-edge exclusivity predicate. -/
theorem sourceReadout_exclusive_of_roles (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed)
    (S : LabelledState (RawLabel v) (strideX*Raster.width v.1+7) (strideY*Raster.height v.1+7))
    (hroles : ∀(g : VertexData) (hg : g∈vertexRecords v.1) (r : Fin 3)
      (h : VertexData) (hh : h∈vertexRecords v.1) (s : Fin 3),
      (g.ports.port r).edge=(h.ports.port s).edge→(g.ports.port r).dir=true→(h.ports.port s).dir=false→
      ¬(gateClaim (observedSignals v g hg S) r=true ∧gateClaim (observedSignals v h hh S) s=true)) :
    PortClaims.Exclusive ((sourceReadout v hw hP hT hG).read S) := by
  intro e he
  obtain ⟨i,hi⟩:=(incidentPort_bijective hG).2 (⟨e,true⟩ : Port (Fin (Word.compile v.1).edgeCount))
  obtain ⟨j,hj⟩:=(incidentPort_bijective hG).2 (⟨e,false⟩ : Port (Fin (Word.compile v.1).edgeCount))
  have hp:=sourceRole_port v.1 hw hP hT i
  have hq:=sourceRole_port v.1 hw hP hT j
  rw [hi] at hp
  rw [hj] at hq
  have hri:=sourceReadout_incidence v hw hP hT hG S i
  have hrj:=sourceReadout_incidence v hw hP hT hG S j
  rw [hi] at hri
  rw [hj] at hrj
  apply hroles (sourceRecord v.1 hP hT i.1) (sourceRecord_mem v.1 hP hT i.1) (sourceRole v.1 hw hP hT i)
    (sourceRecord v.1 hP hT j.1) (sourceRecord_mem v.1 hP hT j.1) (sourceRole v.1 hw hP hT j)
  · exact (congrArg Port.edge hp).trans (congrArg Port.edge hq).symm
  · exact congrArg Port.dir hp
  · exact congrArg Port.dir hq
  · exact ⟨hri ▸he.1,hrj ▸he.2⟩
end PushPuzzle.PushFS.Reduction.PhysicalInventory

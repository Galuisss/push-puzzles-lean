/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.PhysicalCoreLabels
public import PushFS.Reduction.PortTriggerIndex
import Mathlib.Data.List.GetD

/-! Original finite source incidences select their unique actual source-gate trigger boxes. -/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.PhysicalInventory


open Cslib.Complexity.NCL Plan
set_option maxRecDepth 65536
attribute [local irreducible] Raster.width Raster.height

theorem sourceRecord_exists (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) : ∃g∈vertexRecords w,g.index=i.val := by
  have hi : i.val∈List.range (Word.compile w).vertices.length := List.mem_range.mpr i.isLt
  rw [← vertexRecords_indices hP hT] at hi
  exact List.mem_map.mp hi

noncomputable def sourceRecord (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) : VertexData :=
  Classical.choose (sourceRecord_exists w hP hT i)

theorem sourceRecord_mem (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) : sourceRecord w hP hT i∈vertexRecords w :=
  (Classical.choose_spec (sourceRecord_exists w hP hT i)).1

theorem sourceRecord_index (w : Word) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) : (sourceRecord w hP hT i).index=i.val :=
  (Classical.choose_spec (sourceRecord_exists w hP hT i)).2

/-- The chosen physical record retains every weighted port of this exact original source vertex. -/
theorem sourceRecord_ports (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : Fin (Word.compile w).vertices.length) :
    ((Word.compile w).vertices.get i).ports.Perm (sourceRecord w hP hT i).ports.vertex.ports := by
  obtain ⟨_,u,hu,_,hp⟩ := vertexRecord_correct hw hP hT (sourceRecord_mem w hP hT i)
  rw [sourceRecord_index,List.getD_eq_getElem _ _ i.isLt] at hu
  change (Word.compile w).vertices.get i=u at hu
  exact hu.symm ▸ hp

private theorem orderedRole_exists (p : OrderedPorts) (q : WeightedPort ℕ) (hq : q∈p.vertex.ports) :
    ∃r : Fin 3,p.port r=q.port := by
  cases hk : p.isAND <;>
    simp only [OrderedPorts.vertex,hk,Bool.false_eq_true,ite_false,ite_true,Vertex.and,Vertex.or,
      List.mem_cons,List.not_mem_nil,or_false] at hq
  all_goals rcases hq with rfl|rfl|rfl
  all_goals first | exact ⟨0,rfl⟩ | exact ⟨1,rfl⟩ | exact ⟨2,rfl⟩

/-- Each actual finite source incidence occurs at a literal role of its own real placed gate. -/
theorem sourceRole_exists (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : PortIncidence (Word.compile w).graph) :
    ∃r : Fin 3,(sourceRecord w hP hT i.1).ports.port r=(incidentPort (Word.compile w).graph i).map Fin.val := by
  let p := ((Word.compile w).graph i.1).ports.get i.2
  have hp : p∈((Word.compile w).graph i.1).ports := List.get_mem _ i.2
  have hm : p.map Fin.val∈(((Word.compile w).graph i.1).ports.map (WeightedPort.map Fin.val)) :=
    List.mem_map.mpr ⟨p,hp,rfl⟩
  change p.map Fin.val∈(((Word.compile w).graph.map Fin.val) i.1).ports at hm
  rw [(Word.compile w).graph_map_val hw.1] at hm
  exact orderedRole_exists (sourceRecord w hP hT i.1).ports (p.map Fin.val)
    ((sourceRecord_ports w hw hP hT i.1).subset hm)

noncomputable def sourceRole (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : PortIncidence (Word.compile w).graph) : Fin 3 :=
  Classical.choose (sourceRole_exists w hw hP hT i)

theorem sourceRole_port (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (i : PortIncidence (Word.compile w).graph) :
    (sourceRecord w hP hT i.1).ports.port (sourceRole w hw hP hT i)=
      (incidentPort (Word.compile w).graph i).map Fin.val :=
  Classical.choose_spec (sourceRole_exists w hw hP hT i)

theorem port_map_val_injective (n : ℕ) : Function.Injective (Port.map (Fin.val : Fin n→ℕ)) := by
  rintro ⟨e,d⟩ ⟨f,c⟩ he
  simp only [Port.map,Port.mk.injEq] at he ⊢
  exact ⟨Fin.ext he.1,he.2⟩

/-- Well-formedness assigns different source incidences to different actual gate roles. -/
theorem source_role_injective (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (hG : (Word.compile w).graph.WellFormed) :
    Function.Injective (fun i : PortIncidence (Word.compile w).graph=>
      (sourceRecord w hP hT i.1,sourceRole w hw hP hT i)) := by
  intro i j he
  have hp := congrArg (fun p : VertexData×Fin 3=>p.1.ports.port p.2) he
  change (sourceRecord w hP hT i.1).ports.port (sourceRole w hw hP hT i)=
    (sourceRecord w hP hT j.1).ports.port (sourceRole w hw hP hT j) at hp
  rw [sourceRole_port,sourceRole_port] at hp
  exact (incidentPort_bijective hG).1 (port_map_val_injective _ hp)

/-- The original source graph's true endpoint incidences use distinct real physical boxes. -/
noncomputable def sourceTriggers (v : CellPlan.Source) (hw : (Word.compile v.1).Valid)
    (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] []) (hG : (Word.compile v.1).graph.WellFormed) :
    PortIncidence (Word.compile v.1).graph↪RawLabel v :=
  { toFun i := gateTriggers v (⟨sourceRecord v.1 hP hT i.1,sourceRecord_mem v.1 hP hT i.1⟩,sourceRole v.1 hw hP hT i)
    inj' := by
      intro i j he
      have hh := (gateTriggers v).injective he
      exact source_role_injective v.1 hw hP hT hG (congrArg (fun p : GatePort v=>(p.1.val,p.2)) hh) }


/-- Every actual compiled gate has legal canonical flags whenever the original weighted source is legal. -/
theorem record_legal (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (bits : List Bool) (hc : (Word.compile w).checkLegal bits=true)
    (g : VertexData) (hg : g∈vertexRecords w) :
    Gadgets.Gates.legal g.ports.isAND (gateSignals (g.ports,bits)) := by
  obtain ⟨hi,u,hu,hm,hp⟩ := vertexRecord_correct hw hP hT hg
  have hmem : u∈(Word.compile w).vertices := by
    rw [← hu,List.getD_eq_getElem _ _ hi]
    exact List.getElem_mem hi
  have hs := (Vertex.checkSat_eq_true_iff u bits).mp (List.all_eq_true.mp hc u hmem)
  have hn : g.ports.vertex.minInflow=2 := by
    unfold OrderedPorts.vertex
    split <;> rfl
  exact (legal_signals_iff g.ports _).mpr ((Vertex.sat_iff_of_perm hp (hm.trans hn.symm) _).mp hs)

end PushPuzzle.PushFS.Reduction.PhysicalInventory

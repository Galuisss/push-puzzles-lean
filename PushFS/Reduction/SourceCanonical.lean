/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module
public import PushFS.Reduction.PhysicalReadoutClaims
public import PushFS.Reduction.SourceEdgeMetadata
public import PushFS.Reduction.PhysicalProfiles
import Mathlib.Data.List.GetD

/-! Exact finite source configurations, legal complete gate flags and their one-edge canonical changes. -/
@[expose] public section
open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction.SourceCanonical

open Cslib.Complexity.NCL Plan Gadgets PhysicalInventory
set_option maxRecDepth 65536
set_option maxHeartbeats 100000

def configBits {n : ℕ} (c : Fin n→Bool) : List Bool:=List.ofFn c

@[simp] theorem configBits_length {n : ℕ} (c : Fin n→Bool) : (configBits c).length=n:=List.length_ofFn

theorem configBits_getD {n : ℕ} (c : Fin n→Bool) (i : ℕ) (hi : i<n) :
    (configBits c).getD i false=c ⟨i,hi⟩ := by
  rw [List.getD_eq_getElem _ false (by simpa using hi)]
  simp only [configBits,List.getElem_ofFn]

theorem configBits_config (G : AndOrGraph) (bits : List Bool) (hl : bits.length=G.edgeCount) :
    configBits (G.config bits)=bits:=G.ofFn_config bits hl

private theorem checkLegal_configBits (w : Word) (hw : (Word.compile w).Valid)
    (c : Fin (Word.compile w).edgeCount→Bool) (hc : (Word.compile w).graph.Legal c) :
    (Word.compile w).checkLegal (configBits c)=true := by
  apply (AndOrGraph.checkLegal_eq_true_iff _ hw.1 _).mpr
  simpa only [configBits,AndOrGraph.config_ofFn] using hc

/-- Any legal finite source orientation gives the actual complete canonical flag assignment at every emitted gate. -/
theorem gate_legal (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (hc : (Word.compile w).graph.Legal c)
    (g : VertexData) (hg : g∈vertexRecords w) :
    Gates.legal g.ports.isAND (gateSignals (g.ports,configBits c)) :=
  record_legal w hw hP hT (configBits c) (checkLegal_configBits w hw c hc) g hg

theorem configBits_reverse_getD {n : ℕ} (c : Fin n→Bool) (e : Fin n) (i : ℕ) (hi : i<n) :
    (configBits (reverse c e)).getD i false=
      if i=e.val then !((configBits c).getD i false) else (configBits c).getD i false := by
  rw [configBits_getD _ i hi,configBits_getD _ i hi]
  by_cases he : i=e.val
  · have hf : (⟨i,hi⟩ : Fin n)=e:=Fin.ext he
    rw [hf,reverse_self]
    simp only [he,ite_true]
  · rw [reverse_of_ne c (fun hf=>he (congrArg Fin.val hf))]
    simp only [he,ite_false]

private theorem claim_get_equal : ∀(a b : Gates.Signals) (r : Fin 3),
    gateClaim a r=gateClaim b r ↔a.get r=b.get r := by decide +kernel
private theorem claim_get_not : ∀(a b : Gates.Signals) (r : Fin 3),
    gateClaim b r=!(gateClaim a r) ↔b.get r=!(a.get r) := by decide +kernel

/-- Reversing a source edge flips exactly the inward claim at roles that name that original edge. -/
theorem gateClaim_reverse (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (e : Fin (Word.compile w).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3) :
    gateClaim (gateSignals (g.ports,configBits (reverse c e))) r=
      if (g.ports.port r).edge=e.val then !(gateClaim (gateSignals (g.ports,configBits c)) r)
        else gateClaim (gateSignals (g.ports,configBits c)) r := by
  rw [gateSignals_wire_phase,gateSignals_wire_phase,configBits_reverse_getD c e _ (vertexRecord_edge_lt w hw hP hT g hg r)]
  by_cases he : (g.ports.port r).edge=e.val
  · simp only [he,ite_true]
    cases (g.ports.port r).dir <;> simp
  · simp only [he,ite_false]

/-- The physical right flag uses the outward convention and still flips at exactly the same original edge. -/
private theorem gate_get_reverse (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true)
    (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (e : Fin (Word.compile w).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3) :
    (gateSignals (g.ports,configBits (reverse c e))).get r=
      if (g.ports.port r).edge=e.val then !((gateSignals (g.ports,configBits c)).get r)
        else (gateSignals (g.ports,configBits c)).get r := by
  have hh:=gateClaim_reverse w hw hP hT c e g hg r
  by_cases he : (g.ports.port r).edge=e.val
  · simp only [he,ite_true] at hh ⊢
    exact (claim_get_not _ _ r).mp hh
  · simp only [he,ite_false] at hh ⊢
    exact (claim_get_equal _ _ r).mp hh

private theorem signals_ext : ∀(a b : Gates.Signals),(∀r : Fin 3,a.get r=b.get r)→a=b := by decide +kernel

private theorem singleChange_get : ∀(a b : Gates.Signals) (r : Fin 3),
    b.get r=!(a.get r)→(∀s : Fin 3,s≠r→b.get s=a.get s)→Gates.singleChange a b := by decide +kernel

/-- A real gate incident to the reversed original edge has exactly one changed canonical physical role. -/
theorem gate_singleChange (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (e : Fin (Word.compile w).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords w) (r : Fin 3) (he : (g.ports.port r).edge=e.val) :
    Gates.singleChange (gateSignals (g.ports,configBits c)) (gateSignals (g.ports,configBits (reverse c e))) := by
  apply singleChange_get _ _ r
  · simpa only [he,ite_true] using gate_get_reverse w hw hP hT c e g hg r
  · intro s hs
    have hne : (g.ports.port s).edge≠e.val:=fun hh=>hs (vertexRecord_edges_injective hP hT hg (hh.trans he.symm))
    simpa only [hne,ite_false] using gate_get_reverse w hw hP hT c e g hg s

theorem gate_unchanged (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (e : Fin (Word.compile w).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords w) (he : ∀r : Fin 3,(g.ports.port r).edge≠e.val) :
    gateSignals (g.ports,configBits c)=gateSignals (g.ports,configBits (reverse c e)) := by
  apply signals_ext
  intro r
  have hh:=gate_get_reverse w hw hP hT c e g hg r
  simp only [he r,ite_false] at hh
  exact hh.symm

/-- Each legal source step gives legal physical endpoint flags and at most one changed role at every actual gate. -/
theorem step_gates (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    {c d : Fin (Word.compile w).edgeCount→Bool} (hstep : (Word.compile w).graph.Step c d)
    (g : VertexData) (hg : g∈vertexRecords w) :
    Gates.legal g.ports.isAND (gateSignals (g.ports,configBits c)) ∧
    Gates.legal g.ports.isAND (gateSignals (g.ports,configBits d)) ∧
    (gateSignals (g.ports,configBits c)=gateSignals (g.ports,configBits d) ∨
      Gates.singleChange (gateSignals (g.ports,configBits c)) (gateSignals (g.ports,configBits d))) := by
  obtain ⟨hc,hd,e,rfl⟩:=hstep
  refine ⟨gate_legal w hw hP hT c hc g hg,gate_legal w hw hP hT (reverse c e) hd g hg,?_⟩
  by_cases h : ∃r : Fin 3,(g.ports.port r).edge=e.val
  · obtain ⟨r,hr⟩:=h
    exact Or.inr (gate_singleChange w hw hP hT c e g hg r hr)
  · exact Or.inl (gate_unchanged w hw hP hT c e g hg (not_exists.mp h))

private theorem changing_get_ne : ∀a b : Gates.Signals,Gates.singleChange a b→
    a.get (Gates.changingPort a b)≠b.get (Gates.changingPort a b) := by decide +kernel

/-- The macro's selected changing port names exactly the original NCL edge that was reversed. -/
theorem changingPort_edge (w : Word) (hw : (Word.compile w).Valid) (hP : w.checkPlane=true) (hT : w.WellTyped [] [])
    (c : Fin (Word.compile w).edgeCount→Bool) (e : Fin (Word.compile w).edgeCount)
    (g : VertexData) (hg : g∈vertexRecords w)
    (hs : Gates.singleChange (gateSignals (g.ports,configBits c)) (gateSignals (g.ports,configBits (reverse c e)))) :
    (g.ports.port (Gates.changingPort (gateSignals (g.ports,configBits c))
      (gateSignals (g.ports,configBits (reverse c e))))).edge=e.val := by
  by_contra hne
  have he:=gate_get_reverse w hw hP hT c e g hg
    (Gates.changingPort (gateSignals (g.ports,configBits c)) (gateSignals (g.ports,configBits (reverse c e))))
  simp only [hne,ite_false] at he
  exact changing_get_ne _ _ hs he.symm

private theorem canonical_config (v : CellPlan.Source) (hP : v.1.checkPlane=true)
    (hT : v.1.WellTyped [] [])
    (bits : List Bool) (hlen : bits.length=(Word.compile v.1).edgeCount) :
    PhysicalInventory.canonical v hP hT (configBits ((Word.compile v.1).config bits))=
      PhysicalInventory.canonical v hP hT bits :=
  congrArg (PhysicalInventory.canonical v hP hT) (configBits_config (Word.compile v.1) bits hlen)

/-- Serialization of the finite initial orientation recovers the exact original complete physical initial state. -/
theorem canonical_initial_config (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (hlen : v.2.1.length=(Word.compile v.1).edgeCount) :
    PhysicalInventory.canonical v hP hT (configBits ((Word.compile v.1).config v.2.1))=
      (PhysicalInventory.puzzle v hP hT).initial :=
  (canonical_config v hP hT v.2.1 hlen).trans (PhysicalInventory.canonical_initial v hP hT)

/-- Serialization of the finite target orientation recovers the exact original whole-board goals. -/
theorem canonical_target_config (v : CellPlan.Source) (hP : v.1.checkPlane=true) (hT : v.1.WellTyped [] [])
    (hlen : v.2.2.length=(Word.compile v.1).edgeCount) :
    (PhysicalInventory.puzzle v hP hT).board.goals=
      (PhysicalInventory.canonical v hP hT (configBits ((Word.compile v.1).config v.2.2))).boxes := by
  have hgoal:=PhysicalInventory.target_canonical v hP hT v.2.1 v.2.2
  exact hgoal.trans (congrArg State.boxes (canonical_config v hP hT v.2.2 hlen).symm)

/-- Canonical ordinary-wire phase negates the source orientation bit and flips on exactly the reversed edge. -/
theorem wire_phase_reverse {n : ℕ} (c : Fin n→Bool) (e f : Fin n) :
    (!((configBits (reverse c e)).getD f.val false))=
      if f=e then !(!((configBits c).getD f.val false)) else !((configBits c).getD f.val false) := by
  rw [configBits_reverse_getD c e f.val f.isLt]
  by_cases h : f=e
  · subst f
    simp
  · have hne : f.val≠e.val:=fun he=>h (Fin.ext he)
    simp only [h,hne,ite_false]

end PushPuzzle.PushFS.Reduction.SourceCanonical

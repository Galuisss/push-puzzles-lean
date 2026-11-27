/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Context.LocalGraph
public import PushS.Source.Strip.Sweep.Context.Legal
public import PushS.Source.Strip.Sweep.Context.Expansion

/-!
# The actual source graph and the actual strip program

The actual diagram's propagated unit-arc labels identify its legal configurations with the
actual unit subdivision. Subdivision, local certified replacement, and native word compilation
then give one complete dynamic simulation from the original source graph.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Context.unitDiagramSimulation`: the actual unit graph and raw scan diagram.
* `PushPuzzle.NCL.Strip.Sweep.Context.simulation`: the actual source graph and emitted native standard graph.
* `PushPuzzle.NCL.Strip.Sweep.Context.nativeSimulation`: the original native input and that same output graph.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Context.diagram_legal_iff`: exact labeled legality of the actual source diagram.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.Context

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal Diagram ConstraintGraph

variable {A K : ℕ} (C : Context A K)

private theorem empty_unitLegalAt {p : Point}
    (hs : Selection C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) p none) (s : Arc C.environment → Bool) :
    UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) p s := by
  cases hs with
  | empty hv _ hp =>
    intro v hvp
    cases v with
    | inl v =>
      have hh := (centerAt_eq_some C.environment _ p v).mpr ⟨List.mem_finRange _, hvp⟩
      rw [hv] at hh
      cases hh
    | inr j =>
      let a := segmentEquiv C.environment ⟨j.1, j.2.castSucc⟩
      have ha := (joint_arc_iff C.environment j a).mpr (Or.inl rfl)
      have hm : a ∈ (slice C.environment (List.finRange C.source.edgeCount) p).incoming ++
          (slice C.environment (List.finRange C.source.edgeCount) p).outgoing := by
        rcases ha.2 with hl | hu
        · exact List.mem_append_right _ ((mem_slice_outgoing C.environment _ p a).mpr
            ⟨List.mem_finRange _, hl.trans hvp⟩)
        · exact List.mem_append_left _ ((mem_slice_incoming C.environment _ p a).mpr
            ⟨List.mem_finRange _, hu.trans hvp⟩)
      rw [List.head?_eq_none_iff.mp hp] at hm
      exact False.elim (List.not_mem_nil hm)

private theorem emptyLabeling_legal (t : ℤ)
    (hc : classify C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t) = none)
    (s : Arc C.environment → Bool) :
    ((C.emptyDiagram t hc).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.emptyLabeling t hc).label) := by
  simpa only [emptyDiagram, emptyLabeling, frontierColors, frontier] using
    PushPuzzle.NCL.Strip.Sweep.Cell.id_retypeLabeling_legal (fun a : Arc C.environment => C.color a.edge)
      (C.frontier t) (C.frontier (t + 1)) (C.empty_frontier t hc) s

/-- Each actual labeled scan step checks precisely the actual unit vertices at its grid site. -/
private theorem step_unitLegalAt (t : ℤ) (s : Arc C.environment → Bool) :
    ((C.stepDiagram t).graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ (C.stepLabeling t).label) ↔
      UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) (scanPoint K t) s := by
  apply C.frame_cases t (fun f => (f.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ f.labeling.label) ↔
    UnitLegalAt C.environment C.graph (fun e => (C.color e).weight) (scanPoint K t) s)
  · intro hc
    dsimp only [emptyFrame]
    have hs := classify_spec C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t)
    rw [hc] at hs
    constructor
    · intro _
      exact C.empty_unitLegalAt hs s
    · intro _
      exact C.emptyLabeling_legal t hc s
  · intro site hc
    dsimp only [cellFrame]
    have hs := classify_spec C.environment (List.finRange C.vertices.length)
      (List.finRange C.source.edgeCount) (scanPoint K t)
    rw [hc] at hs
    exact (C.cellLabeling_legal t site hc s).trans (C.selection_generator_legal hs s)

private theorem unitPoint_support (v : UnitVertex C.environment) :
    ∃ e, realPoint (unitPoint C.environment v) ∈ support (C.environment.route e) := by
  cases v with
  | inr j => exact ⟨j.1, (C.environment.mem_unitRoute _ _).mp (unitPoint_joint_mem _ j)⟩
  | inl v =>
    let p := C.sourcePort v 0
    have hinc := incidencePort_eq_of_get C.vertices C.wellFormed (fun i => (C.arity i).le) v
      ((0 : Fin 3).cast (C.arity v).symm)
    have hv : C.environment.endpoint p.1.edge p.1.dir = v := hinc.1
    have hm := center_endpoint_mem_unitRoute C.environment p.1.edge p.1.dir
    refine ⟨p.1.edge, (C.environment.mem_unitRoute _ _).mp ?_⟩
    change C.environment.center v ∈ C.environment.unitRoute p.1.edge
    simpa only [hv] using hm

/-- Every vertex of the actual unit graph is processed at an actual finite scan position. -/
private theorem unitPoint_scanned (v : UnitVertex C.environment) :
    ∃ i < scanLength C.environment (List.finRange C.source.edgeCount),
      scanPoint K i = unitPoint C.environment v := by
  obtain ⟨e, he⟩ := C.unitPoint_support v
  have hw := support_scan_window C.environment e he
  have hn : 0 ≤ level K (unitPoint C.environment v) := by
    have ho : 0 ≤ ownerStart C.environment e :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    omega
  have ht := support_scan_end C.environment (List.mem_finRange e) he
  have hy : 0 ≤ (unitPoint C.environment v).2 ∧
      (unitPoint C.environment v).2 ≤ height K := by
    have h := (C.environment.support_window e he).2.2
    simp only [realPoint] at h
    have hb : 4 ≤ (unitPoint C.environment v).2 ∧
        (unitPoint C.environment v).2 ≤ (height K : ℤ) := by exact_mod_cast h
    exact ⟨by omega, hb.2⟩
  refine ⟨(level K (unitPoint C.environment v)).toNat, by omega, ?_⟩
  rw [Int.toNat_of_nonneg hn, scanPoint_level hy]

/-- The actual labeled source diagram checks exactly the actual unit-subdivision graph. -/
theorem diagram_legal_iff (s : Arc C.environment → Bool) :
    (C.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp).Legal (s ∘ C.labeling.label) ↔
      (unitGraph C.environment C.graph (fun e => (C.color e).weight)).Legal s := by
  rw [C.labeling_legal]
  constructor
  · intro h v
    obtain ⟨i, hi, hp⟩ := C.unitPoint_scanned v
    exact (C.step_unitLegalAt i s).mp (h i hi) v hp.symm
  · intro h i _
    exact (C.step_unitLegalAt i s).mpr (fun v _ => h v)

/-- The actual edge-label equivalence preserves and reflects every unit-graph move and path. -/
@[expose] def unitDiagramSimulation :
    ConstraintGraph.Simulation (unitGraph C.environment C.graph (fun e => (C.color e).weight))
      (C.diagram.graph PushPuzzle.NCL.Strip.Sweep.Cell.interp) :=
  ConstraintGraph.Simulation.ofLegalEquiv _ _ C.edgeEquiv.symm (fun s => by
    have he : (C.edgeEquiv : C.diagram.Edge → Arc C.environment) = C.labeling.label :=
      funext C.edgeEquiv_apply
    simpa only [Equiv.symm_symm, he] using C.diagram_legal_iff s)

/-- The actual source graph is simulated by the same emitted standard planar strip program. -/
@[expose] def simulation : ConstraintGraph.Simulation C.graph C.program.compile.graph :=
  ((unitSimulation C.environment C.graph (fun e => (C.color e).weight)
    (fun e => by cases C.color e <;> decide) C.loopFree).trans C.unitDiagramSimulation).trans
      C.expansionSimulation

/-- The original native input is dynamically simulated by its actual emitted strip program. -/
@[expose] def nativeSimulation :
    ConstraintGraph.Simulation C.source.graph C.program.compile.graph :=
  (ConstraintGraph.Simulation.ofLegalEquiv C.source.graph C.graph (Equiv.refl _) (fun s => by
    have he : C.graph = C.source.graph ∘ finCongr List.length_ofFn :=
      funext (List.get_ofFn C.source.graph)
    change C.graph.Legal s ↔ C.source.graph.Legal s
    rw [he]
    exact ConstraintGraph.legal_comp C.source.graph (finCongr List.length_ofFn).surjective s)).trans
      C.simulation

end PushPuzzle.NCL.Strip.Sweep.Context

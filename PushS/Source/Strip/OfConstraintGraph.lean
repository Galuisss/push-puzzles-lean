/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Contact
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Incidence
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.Embedding.Colors
public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.LoopFree

/-!
# Fixed-track environments from actual constraint-graph lists

For each original incidence, scan the vertex list for its endpoint and use its position in that
vertex's existing port list. This retains the input graph's original edge and port names.
Bounded row fibers receive slots through `PushPuzzle.NCL.Strip.Placement.ofRows`.

## Main definitions

* `PushPuzzle.NCL.Strip.ofConstraintGraph`: actual six-point routing environment of a finite constraint graph.

## Main results

* `PushPuzzle.NCL.Strip.incidenceVertex_mem`: chosen endpoints are actual listed incidences.
-/

public section

namespace PushPuzzle.NCL.Strip

open Cslib.Complexity Cslib.Complexity.NCL Cslib Planar.Embedding

section Incidences

variable {m : ℕ} (vs : List (Vertex (Fin m)))
  (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))

include hw in
private theorem exists_endpoint (p : Port (Fin m)) :
    ∃ i : Fin vs.length, p ∈ ((vs.get i).ports.map WeightedPort.port) := by
  have hp := mem_vertexLabels vs hw p
  simp only [Sources.vertexLabels, List.mem_flatMap, List.mem_map] at hp
  obtain ⟨v, hv, x, hx, hp⟩ := hp
  obtain ⟨i, rfl⟩ := List.get_of_mem hv
  exact ⟨i, List.mem_map.mpr ⟨x, hx, hp⟩⟩

/-- Scan the original vertex list for the given incidence. -/
@[expose] def incidenceVertex (p : Port (Fin m)) : Fin vs.length :=
  ((List.finRange vs.length).find? fun i => decide (p ∈ (vs.get i).ports.map WeightedPort.port)).get (by
    obtain ⟨i, hi⟩ := exists_endpoint vs hw p
    exact List.find?_isSome.mpr ⟨i, List.mem_finRange i, by simpa using hi⟩)

/-- The selected vertex contains the original incidence. -/
theorem incidenceVertex_mem (p : Port (Fin m)) :
    p ∈ (vs.get (incidenceVertex vs hw p)).ports.map WeightedPort.port := by
  have hf : ((List.finRange vs.length).find? fun i =>
      decide (p ∈ (vs.get i).ports.map WeightedPort.port)) = some (incidenceVertex vs hw p) :=
    (Option.some_get _).symm
  have h := List.find?_some (p := fun i : Fin vs.length =>
    decide (p ∈ (vs.get i).ports.map WeightedPort.port)) hf
  exact of_decide_eq_true h

/-- Every original occurrence belongs to the selected endpoint, using well-formedness. -/
theorem incidenceVertex_eq_of_mem (p : Port (Fin m)) (i : Fin vs.length)
    (hp : p ∈ (vs.get i).ports.map WeightedPort.port) : incidenceVertex vs hw p = i := by
  have hd := (List.nodup_flatMap.mp (vertexLabels_nodup vs hw)).2
  have he := incidenceVertex_mem vs hw p
  rcases lt_trichotomy (incidenceVertex vs hw p) i with hi | hi | hi
  · exact False.elim ((hd.rel_get_of_lt hi) he hp)
  · exact hi
  · exact False.elim ((hd.rel_get_of_lt hi) hp he)

/-- Position of the original incidence in its selected vertex's existing port list. -/
@[expose] def incidencePort (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3)
    (p : Port (Fin m)) : Fin 3 :=
  ⟨((vs.get (incidenceVertex vs hw p)).ports.map WeightedPort.port).idxOf p,
    (List.idxOf_lt_length_of_mem (incidenceVertex_mem vs hw p)).trans_le
      (by simpa only [List.length_map] using h3 (incidenceVertex vs hw p))⟩

/-- Looking up the assigned local port recovers the original incidence label. -/
private theorem incidencePort_get (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3)
    (p : Port (Fin m)) :
    ((vs.get (incidenceVertex vs hw p)).ports.map WeightedPort.port)[(incidencePort vs hw h3 p).val]?
      = some p := List.getElem?_idxOf (incidenceVertex_mem vs hw p)

/-- An original port-list position is recovered by the actual endpoint and slot scans. -/
theorem incidencePort_eq_of_get (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3)
    (i : Fin vs.length) (k : Fin (vs.get i).ports.length) :
    incidenceVertex vs hw ((vs.get i).ports.get k).1 = i ∧
      (incidencePort vs hw h3 ((vs.get i).ports.get k).1).val = k.val := by
  have hp : ((vs.get i).ports.get k).1 ∈ (vs.get i).ports.map WeightedPort.port :=
    List.mem_map.mpr ⟨_, List.get_mem _ _, rfl⟩
  have hi := incidenceVertex_eq_of_mem vs hw _ i hp
  refine ⟨hi, ?_⟩
  have hn : ((vs.get i).ports.map WeightedPort.port).Nodup :=
    (List.nodup_flatMap.mp (vertexLabels_nodup vs hw)).1 _ (List.get_mem _ _)
  simp only [incidencePort, hi]
  simpa only [List.getElem_map, List.get_eq_getElem] using
    hn.idxOf_getElem k.val (by simpa only [List.length_map] using k.isLt)

private theorem incidence_injective (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3) :
    Function.Injective (fun p : Fin m × Bool =>
      (incidenceVertex vs hw ⟨p.1, p.2⟩, incidencePort vs hw h3 ⟨p.1, p.2⟩)) := by
  intro p q h
  have hv := congrArg Prod.fst h
  have hs := congrArg (fun x => (x.2 : Fin 3).val) h
  change incidenceVertex vs hw ⟨p.1, p.2⟩ = incidenceVertex vs hw ⟨q.1, q.2⟩ at hv
  change (incidencePort vs hw h3 ⟨p.1, p.2⟩).val =
    (incidencePort vs hw h3 ⟨q.1, q.2⟩).val at hs
  have hp := incidencePort_get vs hw h3 ⟨p.1, p.2⟩
  rw [hv, hs] at hp
  have he := Option.some.inj (hp.symm.trans (incidencePort_get vs hw h3 ⟨q.1, q.2⟩))
  exact Prod.ext (congrArg Port.edge he) (congrArg Port.dir he)

end Incidences

/-- Construct the actual parity-track environment from finite constraint-graph data.
The supplied row bounds hold for all original port occurrences. -/
@[expose] def ofConstraintGraph {m A K : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3)
    (vertexRows : Fin vs.length → ℕ) (ownerRows : Fin m → ℕ)
    (hA : ∀ r, Fintype.card {i // vertexRows i = r} ≤ A)
    (hK : ∀ r, Fintype.card {e // ownerRows e = r} ≤ K)
    (hrows : ∀ i p, p ∈ (vs.get i).ports →
      ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1) :
    Environment (Fin vs.length) (Fin m) A K where
  vertices := PushPuzzle.NCL.Strip.Placement.ofRows vertexRows hA
  edges := PushPuzzle.NCL.Strip.Placement.ofRows ownerRows hK
  endpoint e d := incidenceVertex vs hw ⟨e, d⟩
  port e d := incidencePort vs hw h3 ⟨e, d⟩
  incidence_injective := by exact incidence_injective vs hw h3
  loopFree e := by
    intro he
    have hf := incidenceVertex_mem vs hw ⟨e, false⟩
    have ht := incidenceVertex_mem vs hw ⟨e, true⟩
    rw [← he] at ht
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hf
    obtain ⟨q, hq, hqe⟩ := List.mem_map.mp ht
    have hpq : p = q := List.inj_on_of_nodup_map (hl _) hp hq (by simp only [hpe, hqe])
    have hd := congrArg (fun x => x.1.dir) hpq
    simp only [hpe, hqe, Bool.false_eq_true] at hd
  endpoint_rows e d := by
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp (incidenceVertex_mem vs hw ⟨e, d⟩)
    simpa only [hpe, PushPuzzle.NCL.Strip.Placement.ofRows_row] using hrows (incidenceVertex vs hw ⟨e, d⟩) p hp

end PushPuzzle.NCL.Strip

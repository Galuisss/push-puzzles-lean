/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.OfConstraintGraph
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import Mathlib.Data.List.GetD

/-!
# Explicit incidence scans in the original vertex list

Scan the original indexed vertex records for a port, then read its position in that vertex's
original port list. These total scans use the existing standard vertex/port encodings. Their
values agree with the actual fixed-track environment's endpoint and port-slot scans.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.endpointIndex`: original vertex index selected by an incidence scan.
* `PushPuzzle.NCL.Strip.PolyTime.portIndex`: the incidence's original local port-list position.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.computableInPolyTime_endpointIndex`, `.computableInPolyTime_portIndex`:
  standard encoded polynomial-time incidence scans.
* `PushPuzzle.NCL.Strip.PolyTime.endpointIndex_eq_incidenceVertex`: exact actual endpoint selection.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

private def endpointCandidates {E : Type*} [DecidableEq E] (vs : List (Vertex E))
    (p : Port E) : List ℕ :=
  (vs.zipIdx.filter (fun vi => (vi.1.ports.map WeightedPort.port).contains p)).map Prod.snd

/-- Scan the original indexed vertex list for the first vertex containing the given incidence. -/
@[expose] def endpointIndex {E : Type*} [DecidableEq E] (vs : List (Vertex E)) (p : Port E) : ℕ :=
  ((vs.zipIdx.filter (fun vi => (vi.1.ports.map WeightedPort.port).contains p)).map Prod.snd).headD 0

/-- Read the given incidence's original port-list index in its scanned endpoint vertex. -/
@[expose] def portIndex {E : Type*} [DecidableEq E] (vs : List (Vertex E)) (p : Port E) : ℕ :=
  ((vs.getD (endpointIndex vs p) ⟨[], 0⟩).ports.map WeightedPort.port).idxOf p

/-- The explicit original endpoint scan is polynomial-time for standard binary vertex/port data.
-/
theorem computableInPolyTime_endpointIndex :
    ComputableInPolyTime (fun p : List (Vertex ℕ) × Port ℕ => endpointIndex p.1 p.2)
      (encPair (encList (encVertex encNat)) (encPort encNat)) encUnary := by
  have hf : ComputableInPolyTime (fun p : List (Vertex ℕ) × Port ℕ =>
      p.1.zipIdx.filter (fun vi => (vi.1.ports.map WeightedPort.port).contains p.2))
      (encPair (encList (encVertex encNat)) (encPort encNat))
      (encList (encPair (encVertex encNat) encUnary)) := by
    apply ComputableInPolyTime.filterWithInput
    · fun_prop
    · fun_prop
  unfold endpointIndex
  fun_prop

/-- The original local port-list index is polynomial-time under standard vertex/port codes. -/
theorem computableInPolyTime_portIndex :
    ComputableInPolyTime (fun p : List (Vertex ℕ) × Port ℕ => portIndex p.1 p.2)
      (encPair (encList (encVertex encNat)) (encPort encNat)) encUnary := by
  have he := computableInPolyTime_endpointIndex
  unfold portIndex
  fun_prop

private theorem mem_endpointCandidates {E : Type*} [DecidableEq E] (vs : List (Vertex E))
    (p : Port E) (j : ℕ) : j ∈ endpointCandidates vs p ↔
      ∃ v, (v, j) ∈ vs.zipIdx ∧ p ∈ v.ports.map WeightedPort.port := by
  simp only [endpointCandidates, List.mem_map, List.mem_filter, Prod.exists,
    List.contains_iff_mem, exists_eq_right]

private theorem endpointIndex_eq_of_unique {E : Type*} [DecidableEq E] (vs : List (Vertex E))
    (p : Port E) (i : Fin vs.length) (hp : p ∈ (vs.get i).ports.map WeightedPort.port)
    (hu : ∀ j : Fin vs.length, p ∈ (vs.get j).ports.map WeightedPort.port → j = i) :
    endpointIndex vs p = i.val := by
  have hi : i.val ∈ endpointCandidates vs p := by
    apply (mem_endpointCandidates vs p i.val).mpr
    refine ⟨vs.get i, ?_, hp⟩
    apply List.mk_mem_zipIdx_iff_getElem?.mpr
    simp [List.get_eq_getElem]
  cases hs : endpointCandidates vs p with
  | nil => simp only [hs, List.not_mem_nil] at hi
  | cons j js =>
    have hj : j ∈ endpointCandidates vs p := hs ▸ List.mem_cons_self
    obtain ⟨v, hv, hpv⟩ := (mem_endpointCandidates vs p j).mp hj
    obtain ⟨hjlt, hv⟩ := List.mem_zipIdx' hv
    have he := hu ⟨j, hjlt⟩ (by simpa only [List.get_eq_getElem, hv] using hpv)
    change (endpointCandidates vs p).headD 0 = i.val
    rw [hs]
    exact congrArg Fin.val he

/-- The total explicit endpoint scan returns the actual fixed-track construction's endpoint. -/
theorem endpointIndex_eq_incidenceVertex {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i)) (p : Port (Fin m)) :
    endpointIndex vs p = (incidenceVertex vs hw p).val := by
  apply endpointIndex_eq_of_unique vs p _ (incidenceVertex_mem vs hw p)
  intro j hj
  exact (incidenceVertex_eq_of_mem vs hw p j hj).symm

/-- The same explicit local scan returns the original construction's actual local port slot. -/
theorem portIndex_eq_incidencePort {m : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3) (p : Port (Fin m)) :
    portIndex vs p = (incidencePort vs hw h3 p).val := by
  unfold portIndex
  rw [endpointIndex_eq_incidenceVertex vs hw]
  rw [List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (incidenceVertex vs hw p).isLt, Option.getD_some]
  rfl

private theorem port_mem_map {E F : Type*} (f : E → F) (hf : Function.Injective f)
    (v : Vertex E) (p : Port E) :
    p.map f ∈ (v.map f).ports.map WeightedPort.port ↔ p ∈ v.ports.map WeightedPort.port := by
  have he : (v.map f).ports.map WeightedPort.port = (v.ports.map WeightedPort.port).map (Port.map f) := by
    simp only [Vertex.map, List.map_map, Function.comp_def, WeightedPort.map]
  rw [he]
  constructor
  · intro h
    obtain ⟨q, hq, hqp⟩ := List.mem_map.mp h
    exact (PushPuzzle.NCL.port_map_injective hf hqp) ▸ hq
  · intro h
    exact List.mem_map_of_mem h

/-- Injectively erasing edge bounds retains the actual selected original vertex index. -/
theorem endpointIndex_map {E F : Type*} [DecidableEq E] [DecidableEq F]
    (f : E → F) (hf : Function.Injective f) (vs : List (Vertex E)) (p : Port E) :
    endpointIndex (vs.map (Vertex.map f)) (p.map f) = endpointIndex vs p := by
  unfold endpointIndex
  simp only [List.zipIdx_map, List.filter_map, List.map_map]
  change ((vs.zipIdx.filter (fun vi =>
    ((vi.1.map f).ports.map WeightedPort.port).contains (p.map f))).map Prod.snd).headD 0 = _
  have he : (vs.zipIdx.filter (fun vi =>
      ((vi.1.map f).ports.map WeightedPort.port).contains (p.map f))) =
      vs.zipIdx.filter (fun vi => (vi.1.ports.map WeightedPort.port).contains p) := by
    apply List.filter_congr
    intro vi _
    rw [Bool.eq_iff_iff, List.contains_iff_mem, List.contains_iff_mem]
    exact port_mem_map f hf vi.1 p
  rw [he]

/-- Injectively erasing edge bounds retains the actual original local port-list position. -/
theorem portIndex_map {E F : Type*} [DecidableEq E] [DecidableEq F]
    (f : E → F) (hf : Function.Injective f) (vs : List (Vertex E)) (p : Port E) :
    portIndex (vs.map (Vertex.map f)) (p.map f) = portIndex vs p := by
  unfold portIndex
  rw [endpointIndex_map f hf]
  have hd : (⟨[], 0⟩ : Vertex F) = (⟨[], 0⟩ : Vertex E).map f := rfl
  rw [hd, List.getD_map]
  have he (v : Vertex E) :
      (v.map f).ports.map WeightedPort.port = (v.ports.map WeightedPort.port).map (Port.map f) := by
    simp only [Vertex.map, List.map_map, Function.comp_def, WeightedPort.map]
  rw [he]
  unfold List.idxOf
  rw [List.findIdx_map]
  congr 1
  funext q
  rw [Bool.eq_iff_iff]
  simp only [Function.comp_def, beq_iff_eq]
  exact (PushPuzzle.NCL.port_map_injective hf).eq_iff

end PushPuzzle.NCL.Strip.PolyTime

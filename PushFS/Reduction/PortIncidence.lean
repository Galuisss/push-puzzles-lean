/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.ConstraintGraph.WellFormed
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.EquivFin

/-!
# Actual source incidences indexed by endpoint ports

The upstream well-formedness condition counts one occurrence of each direction
of every edge. It gives a bijection between vertex-list positions and reference
ports. Physical trigger identities can therefore be attached to real source
ports without merging the two endpoints or assuming an ordering of vertices.
-/

@[expose] public section

open Cslib.Complexity

namespace PushPuzzle.PushFS.Reduction


open Cslib.Complexity.NCL
open scoped BigOperators

variable {V E : Type*}

/-- One actual position in one actual source vertex's weighted port list. -/
abbrev PortIncidence (G : ConstraintGraph V E) := (v : V) × Fin (G v).ports.length

/-- The exact reference port stored at that source incidence. -/
def incidentPort (G : ConstraintGraph V E) (i : PortIncidence G) : Port E :=
  ((G i.1).ports.get i.2).port

/-- Port data are exactly an edge and a direction bit. -/
private def portProduct (E : Type*) : Port E ≃ E × Bool where
  toFun p := (p.edge, p.dir)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Every endpoint of every declared edge is a real occurrence in the source graph. -/
theorem incidentPort_surjective [Fintype V] [Fintype E] {G : ConstraintGraph V E}
    (hG : G.WellFormed) : Function.Surjective (incidentPort G) := by
  classical
  obtain ⟨weight, hw⟩ := hG
  intro p
  have hm : (⟨p, weight p.edge⟩ : WeightedPort E) ∈ G.portMultiset := by
    rw [hw]
    apply Multiset.mem_sum.mpr
    refine ⟨p.edge, Finset.mem_univ _, ?_⟩
    cases p with
    | mk edge dir => cases dir <;> simp
  rw [ConstraintGraph.portMultiset, Multiset.mem_sum] at hm
  obtain ⟨v, _, hv⟩ := hm
  have hp : (⟨p, weight p.edge⟩ : WeightedPort E) ∈ (G v).ports := by simpa using hv
  obtain ⟨i, hi⟩ := List.get_of_mem hp
  refine ⟨⟨v, i⟩, ?_⟩
  exact congrArg WeightedPort.port hi

/-- The number of actual source incidences is the number of edge-direction pairs. -/
private theorem card_portIncidence [Fintype V] [Fintype E] {G : ConstraintGraph V E}
    (hG : G.WellFormed) : Fintype.card (PortIncidence G) = 2 * Fintype.card E := by
  have hh := hG.card_portMultiset
  simpa only [PortIncidence, Fintype.card_sigma, Fintype.card_fin,
    ConstraintGraph.portMultiset, Multiset.card_sum, Multiset.coe_card] using hh

/-- Well-formedness prevents different source incidences from naming the same reference port. -/
theorem incidentPort_bijective [Fintype V] [Fintype E] {G : ConstraintGraph V E}
    (hG : G.WellFormed) : Function.Bijective (incidentPort G) := by
  classical
  let : Fintype (Port E) := Fintype.ofEquiv (E × Bool) (portProduct E).symm
  have hc : Fintype.card (PortIncidence G) = Fintype.card (Port E) := by
    rw [card_portIncidence hG, Fintype.card_congr (portProduct E)]
    simp [Nat.mul_comm]
  have hs := incidentPort_surjective hG
  exact ⟨((Fintype.bijective_iff_surjective_and_card (incidentPort G)).mpr ⟨hs, hc⟩).1, hs⟩

/-- Use the true unique source incidence as the proof index of a physical port trigger. -/
noncomputable def portIncidenceEquiv [Fintype V] [Fintype E] {G : ConstraintGraph V E}
    (hG : G.WellFormed) : PortIncidence G ≃ Port E :=
  Equiv.ofBijective (incidentPort G) (incidentPort_bijective hG)

end PushPuzzle.PushFS.Reduction

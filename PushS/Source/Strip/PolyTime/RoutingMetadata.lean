/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.Carrier
public import PushS.Source.Strip.PolyTime.Incidence
public import PushS.Source.Strip.PolyTime.Slots
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Actual carrier inputs from standard source data

The internal algorithm input is the original vertex list and the two actual row arrays. Scan
original incidences, retain their original port-list slots, and compute the same panel addresses
and parity tracks. The resulting standard encoded carrier compiler is polynomial-time.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata`: original vertex records and actual source/owner row arrays.
* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.carrier`: actual explicit six-point input for one original edge.
* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes`: full actual point lists in original edge order.
* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.ofFinite`: erase only the finite bounds of source edge labels.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.computableInPolyTime_carrier`: standard encoded carrier data.
* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.carrier_ofFinite`: same original routing environment fields.
* `PushPuzzle.NCL.Strip.PolyTime.RoutingMetadata.unitRoutes_ofFinite`: same complete original unit routes.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

/-- Original source data consumed by the explicit carrier-emission algorithm. -/
@[ext] structure RoutingMetadata where
  /-- Actual original vertex records, with their original binary edge names and port order. -/
  vertices : List (Vertex ℕ)
  /-- Source panel of each original vertex, in the same original vertex order. -/
  vertexRows : List ℕ
  /-- Owner panel of each original edge, in the same original edge order. -/
  ownerRows : List ℕ

/-- Original standard binary vertex records and two explicit unary row arrays. -/
enc_structure encRoutingMetadata : RoutingMetadata where
  vertices : (encList (encVertex encNat)), vertexRows : (encList encUnary),
  ownerRows : (encList encUnary)

namespace RoutingMetadata

open Cslib.Complexity Cslib.Complexity.NCL

/-- Read a three-slot port index, using the final slot for indices at least two. -/
@[expose] def portSlot (n : ℕ) : Fin 3 := if n = 0 then 0 else if n = 1 then 1 else 2

private theorem portSlot_val (s : Fin 3) : portSlot s.val = s := by
  fin_cases s <;> rfl

private theorem computableInPolyTime_portSlot :
    ComputableInPolyTime portSlot encUnary (encFinEnum (Fin 3)) := by
  unfold portSlot
  fun_prop

/-- Compute the actual parity track and original endpoint addresses/slots for one edge. -/
@[expose] def carrier (A K : ℕ) (data : RoutingMetadata) (e : ℕ) : Carrier where
  track := K * (data.ownerRows.getD e 0 % 2) + slot data.ownerRows e
  source := address A data.vertexRows (endpointIndex data.vertices ⟨e, false⟩)
  target := address A data.vertexRows (endpointIndex data.vertices ⟨e, true⟩)
  sourcePort := portSlot (portIndex data.vertices ⟨e, false⟩)
  targetPort := portSlot (portIndex data.vertices ⟨e, true⟩)

/-- The same actual carrier metadata is polynomial-time in the original graph and row arrays. -/
theorem computableInPolyTime_carrier (A K : ℕ) :
    ComputableInPolyTime (fun p : RoutingMetadata × ℕ => carrier A K p.1 p.2)
      (encPair encRoutingMetadata encUnary) encCarrier := by
  have hp (d : Bool) : ComputableInPolyTime (fun p : RoutingMetadata × ℕ =>
      (p.1.vertices, (⟨p.2, d⟩ : Port ℕ))) (encPair encRoutingMetadata encUnary)
      (encPair (encList (encVertex encNat)) (encPort encNat)) := by
    have he := ComputableInPolyTime.unary_to_binary.comp
      (ComputableInPolyTime.snd encRoutingMetadata encUnary)
    fun_prop
  have he (d : Bool) : ComputableInPolyTime (fun p : RoutingMetadata × ℕ =>
      endpointIndex p.1.vertices ⟨p.2, d⟩) (encPair encRoutingMetadata encUnary) encUnary := by
    simpa only [Function.comp_def] using computableInPolyTime_endpointIndex.comp (hp d)
  have hs (d : Bool) : ComputableInPolyTime (fun p : RoutingMetadata × ℕ =>
      portSlot (portIndex p.1.vertices ⟨p.2, d⟩)) (encPair encRoutingMetadata encUnary)
      (encFinEnum (Fin 3)) := by
    simpa only [Function.comp_def] using computableInPolyTime_portSlot.comp
      (computableInPolyTime_portIndex.comp (hp d))
  have ha (d : Bool) : ComputableInPolyTime (fun p : RoutingMetadata × ℕ =>
      address A p.1.vertexRows (endpointIndex p.1.vertices ⟨p.2, d⟩))
      (encPair encRoutingMetadata encUnary) encUnary := by
    simpa only [Function.comp_def] using (computableInPolyTime_address A).comp
      ((encRoutingMetadata_vertexRows_polyTime (ComputableInPolyTime.fst _ _)).prod (he d))
  have hslot := computableInPolyTime_slot.comp
    ((encRoutingMetadata_ownerRows_polyTime (ComputableInPolyTime.fst _ _)).prod
      (ComputableInPolyTime.snd encRoutingMetadata encUnary))
  unfold carrier
  apply encCarrier_mk_polyTime
  · fun_prop
  · exact ha false
  · exact ha true
  · exact hs false
  · exact hs true

/-- Compile all original carriers in their actual original-edge order. -/
@[expose] def unitRoutes (A K : ℕ) (data : RoutingMetadata) : List Cslib.Orthogonal.Route :=
  (List.range data.ownerRows.length).map fun e =>
    PushPuzzle.NCL.Strip.PolyTime.Carrier.unitRoute (PushPuzzle.NCL.Strip.Environment.routeBudget A K) (carrier A K data e)

/-- The complete original carrier point arrays emit in standard polynomial time. -/
theorem computableInPolyTime_unitRoutes (A K : ℕ) :
    ComputableInPolyTime (unitRoutes A K) encRoutingMetadata (encList encRoute) := by
  unfold unitRoutes
  apply ComputableInPolyTime.mapWithInput
  · fun_prop
  · simpa only [Function.comp_def] using
      (PushPuzzle.NCL.Strip.PolyTime.Carrier.computableInPolyTime_unitRoute (PushPuzzle.NCL.Strip.Environment.routeBudget A K)).comp
        (computableInPolyTime_carrier A K)

/-- Erase finite edge bounds and retain both actual row arrays in their original order. -/
@[expose] def ofFinite {m : ℕ} (vs : List (Vertex (Fin m)))
    (vertexRows : Fin vs.length → ℕ) (ownerRows : Fin m → ℕ) : RoutingMetadata where
  vertices := vs.map (Vertex.map Fin.val)
  vertexRows := List.ofFn vertexRows
  ownerRows := List.ofFn ownerRows

section Finite

variable {m A K : ℕ} (vs : List (Vertex (Fin m)))
    (hw : ConstraintGraph.WellFormed (fun i : Fin vs.length => vs.get i))
    (hl : ConstraintGraph.LoopFree (fun i : Fin vs.length => vs.get i))
    (h3 : ∀ i : Fin vs.length, (vs.get i).ports.length ≤ 3)
    (vertexRows : Fin vs.length → ℕ) (ownerRows : Fin m → ℕ)
    (hA : ∀ row, Fintype.card {i // vertexRows i = row} ≤ A)
    (hK : ∀ row, Fintype.card {e // ownerRows e = row} ≤ K)
    (hrows : ∀ i p, p ∈ (vs.get i).ports →
      ownerRows p.1.edge ≤ vertexRows i ∧ vertexRows i ≤ ownerRows p.1.edge + 1)

/-- The explicit standard-data scans produce exactly the actual routing environment fields. -/
theorem carrier_ofFinite (e : Fin m) :
    carrier A K (ofFinite vs vertexRows ownerRows) e.val =
      PushPuzzle.NCL.Strip.PolyTime.Carrier.ofEnvironment (ofConstraintGraph vs hw hl h3 vertexRows ownerRows hA hK hrows) e := by
  have he (d : Bool) : endpointIndex (vs.map (Vertex.map Fin.val)) ⟨e.val, d⟩ =
      (incidenceVertex vs hw ⟨e, d⟩).val := by
    change endpointIndex (vs.map (Vertex.map Fin.val)) ((⟨e, d⟩ : Port (Fin m)).map Fin.val) = _
    rw [endpointIndex_map _ Fin.val_injective, endpointIndex_eq_incidenceVertex vs hw]
  have hp (d : Bool) : portSlot (portIndex (vs.map (Vertex.map Fin.val)) ⟨e.val, d⟩) =
      incidencePort vs hw h3 ⟨e, d⟩ := by
    change portSlot (portIndex (vs.map (Vertex.map Fin.val))
      ((⟨e, d⟩ : Port (Fin m)).map Fin.val)) = _
    rw [portIndex_map _ Fin.val_injective, portIndex_eq_incidencePort vs hw h3, portSlot_val]
  have hr : (List.ofFn ownerRows).getD e.val 0 = ownerRows e := by
    simp [List.getD_eq_getElem?_getD, e.isLt]
  change _ =
    ({ track := K * (ownerRows e % 2) + ((PushPuzzle.NCL.Strip.Placement.ofRows ownerRows hK).slot e).val,
       source := (PushPuzzle.NCL.Strip.Placement.ofRows vertexRows hA).address (incidenceVertex vs hw ⟨e, false⟩),
       target := (PushPuzzle.NCL.Strip.Placement.ofRows vertexRows hA).address (incidenceVertex vs hw ⟨e, true⟩),
       sourcePort := incidencePort vs hw h3 ⟨e, false⟩,
       targetPort := incidencePort vs hw h3 ⟨e, true⟩ } : Carrier)
  simp only [carrier, ofFinite, he, hp, hr, ofRows_slot, ofRows_address]

private theorem unitRoute_ofFinite (e : Fin m) :
    PushPuzzle.NCL.Strip.PolyTime.Carrier.unitRoute (PushPuzzle.NCL.Strip.Environment.routeBudget A K)
      (carrier A K (ofFinite vs vertexRows ownerRows) e.val) =
        (ofConstraintGraph vs hw hl h3 vertexRows ownerRows hA hK hrows).unitRoute e := by
  rw [carrier_ofFinite vs hw hl h3 vertexRows ownerRows hA hK hrows]
  exact PushPuzzle.NCL.Strip.PolyTime.Carrier.unitRoute_ofEnvironment _ e

/-- The standard-data compiler returns all complete original carrier traversals in exact order.
-/
theorem unitRoutes_ofFinite :
    unitRoutes A K (ofFinite vs vertexRows ownerRows) =
      List.ofFn (ofConstraintGraph vs hw hl h3 vertexRows ownerRows hA hK hrows).unitRoute := by
  apply List.ext_getElem
  · simp only [unitRoutes, ofFinite, List.length_map, List.length_range, List.length_ofFn]
  intro i hi hj
  have him : i < m := by
    simpa only [unitRoutes, ofFinite, List.length_map, List.length_range, List.length_ofFn] using hi
  simpa only [unitRoutes, ofFinite, List.length_ofFn, List.getElem_map, List.getElem_range,
    List.getElem_ofFn] using
    unitRoute_ofFinite vs hw hl h3 vertexRows ownerRows hA hK hrows ⟨i, him⟩

end Finite

end RoutingMetadata
end PushPuzzle.NCL.Strip.PolyTime

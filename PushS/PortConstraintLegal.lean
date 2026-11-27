/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortConstraintBounds
public import PushS.PortInputLegal
import all PushS.PortConstraintGraph

/-!
# Exact native legality of the same actual port constraints

The standard graph's upper and lower native records express exactly the existing interface
thresholds. Erasing its finite edge bounds retains the same original port labels and direction
vector, giving the native legality equivalence for the actual full-length axis arrays.

## Main results

* `PortLayout.graphData_legal_iff`: standard native legality is precisely `InputLegal`.
-/

public section

namespace PushPuzzle.PushS.PortLayout

open Cslib.Complexity

private theorem native_legal_iff (g : NCL.AndOrGraph) (hb : g.Bounded) (axes : List Bool) :
    g.graph.Legal (g.config axes) ↔
      ∀ v ∈ g.vertices, v.Sat (fun edge => axes.getD edge false) := by
  rw [List.forall_mem_iff_get]
  have hm := NCL.ConstraintGraph.legal_map g.graph Fin.val (fun edge => axes.getD edge false)
  rw [g.graph_map_val hb] at hm
  exact hm.symm

private theorem upper_sat (a b : ℕ) (s : ℕ → Bool) :
    (upperVertex (a, b)).Sat s ↔ s a = true ∨ s b = true := by
  cases ha : s a <;> cases hb : s b <;>
    simp [upperVertex, NCL.Vertex.Sat, NCL.Vertex.inflow, NCL.Port.In, ha, hb]

private theorem lower_wire_sat (a b : ℕ) (s : ℕ → Bool) :
    (lowerVertex (.wire a b)).Sat s ↔ s a = false ∨ s b = false := by
  cases ha : s a <;> cases hb : s b <;>
    simp [lowerVertex, NCL.Vertex.Sat, NCL.Vertex.inflow, NCL.Port.In, ha, hb]

private theorem and_sat (first : ℕ) (s : ℕ → Bool) :
    (lowerVertex (.gate .andGate first)).Sat s ↔
      s (first + 2) = false ∨ (s first = false ∧ s (first + 1) = false) := by
  simp only [lowerVertex, gateVertex, ite_true, NCL.Vertex.sat_and, NCL.Port.In]

private theorem or_sat (first : ℕ) (s : ℕ → Bool) :
    (lowerVertex (.gate .orGate first)).Sat s ↔
      s first = false ∨ s (first + 1) = false ∨ s (first + 2) = false := by
  simp only [lowerVertex, gateVertex, reduceCtorEq, ite_false, NCL.Vertex.sat_or, NCL.Port.In]

/-- The same full-length actual axis vector is legal in the standard native graph exactly when
it satisfies the existing actual upper/lower interface thresholds. -/
theorem graphData_legal_iff (l : PortLayout) (hb : l.graphData.Bounded) (axes : List Bool)
    (hlen : axes.length = l.portCount) :
    l.graphData.graph.Legal (l.graphData.config axes) ↔ l.InputLegal axes := by
  rw [native_legal_iff l.graphData hb]
  constructor
  · intro h
    have hu (a b : ℕ) (hm : (a, b) ∈ l.upperPairs) :
        (upperVertex (a, b)).Sat (fun edge => axes.getD edge false) :=
      h _ (List.mem_append_left _ (List.mem_map.mpr ⟨(a, b), hm, rfl⟩))
    have hl (group : LowerGroup) (hm : group ∈ l.lowerGroups) :
        (lowerVertex group).Sat (fun edge => axes.getD edge false) :=
      h _ (List.mem_append_right _ (List.mem_map.mpr ⟨group, hm, rfl⟩))
    exact
      { axes_length := hlen
        upper := fun a b hm => (upper_sat a b _).mp (hu a b hm)
        lower_wire := fun a b hm => (lower_wire_sat a b _).mp (hl (.wire a b) hm)
        or_gate := fun first hm => (or_sat first _).mp (hl (.gate .orGate first) hm)
        and_gate := fun first hm => (and_sat first _).mp (hl (.gate .andGate first) hm) }
  · intro h v hv
    change v ∈ l.upperPairs.map upperVertex ++ l.lowerGroups.map lowerVertex at hv
    rcases List.mem_append.mp hv with hv | hv
    · obtain ⟨⟨a, b⟩, hab, rfl⟩ := List.mem_map.mp hv
      exact (upper_sat a b _).mpr (h.upper a b hab)
    · obtain ⟨group, hgroup, rfl⟩ := List.mem_map.mp hv
      cases group with
      | wire a b => exact (lower_wire_sat a b _).mpr (h.lower_wire a b hgroup)
      | gate kind first =>
        cases kind with
        | andGate => exact (and_sat first _).mpr (h.and_gate first hgroup)
        | orGate => exact (or_sat first _).mpr (h.or_gate first hgroup)

end PushPuzzle.PushS.PortLayout

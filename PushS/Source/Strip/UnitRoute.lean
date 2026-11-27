/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Environment
public import CslibFrontier.Foundations.Geometry.Orthogonal.Subdivision
public import CslibFrontier.Foundations.Geometry.Orthogonal.Neighborhood
public import CslibFrontier.Foundations.Geometry.Orthogonal.Macrocell
import Mathlib.Tactic.Linarith

/-!
# Actual unit subdivisions of the strip carriers

The general integer-route subdivision permits either direction on either coordinate. It retains
the carrier's full real support and lists each visited grid point once. Its explicit indices
therefore supply the order of crossing sites along the original edge.

## Main definitions

* `PushPuzzle.NCL.Strip.Environment.unitRoute`: actual unit subdivision of a six-point carrier.

## Main results

* `PushPuzzle.NCL.Strip.Environment.mem_unitRoute`: exact grid-point membership in the original real support.
* `PushPuzzle.NCL.Strip.Environment.unitRoute_nodup`: the route order has no repeated grid points.
-/

public section

namespace PushPuzzle.NCL.Strip.Environment

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Uniform total-wire budget determined by the fixed panel and track capacities. -/
@[expose] def routeBudget (A K : ℕ) : ℕ := 5 * (16 * A + 4 * K + 8)

/-- Each carrier has bounded total Manhattan length, independently of its owner row. -/
private theorem wireLength_route_le (e : E) : wireLength (R.route e) ≤ routeBudget A K := by
  let offset : Point := (-8 * (A : ℤ) * R.edges.row e, 0)
  have hb : ∀ p ∈ translate offset (R.route e),
      0 ≤ p.1 ∧ p.1 ≤ 16 * (A : ℤ) ∧ 0 ≤ p.2 ∧ p.2 ≤ 4 * (K : ℤ) + 8 := by
    intro p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    have h := R.point_window e hq
    simp only [offset, Prod.fst_add, Prod.snd_add, add_zero]
    constructor <;> (try constructor) <;> (try constructor) <;> nlinarith
  have hw := wireLength_le_box (r := translate offset (R.route e))
    (w := 16 * A) (h := 4 * K + 8) (fun p hp => by exact_mod_cast hb p hp)
  rw [wireLength_translate, consecutivePairs_length_translate] at hw
  change wireLength (R.route e) ≤ 5 * (16 * A + (4 * K + 8)) at hw
  simpa only [routeBudget, Nat.add_assoc] using hw

/-- Actual unit grid points in traversal order from the original false endpoint to the true one.
-/
@[expose] def unitRoute (e : E) : Route := subdivide (R.route e)

/-- The actual unit route has the complete real support of its six-point carrier. -/
private theorem support_unitRoute (e : E) : support (R.unitRoute e) = support (R.route e) :=
  support_subdivide (R.route_orthogonal e)

/-- The unit route lists exactly the integer points of the original continuous carrier. -/
theorem mem_unitRoute (e : E) (p : Point) :
    p ∈ R.unitRoute e ↔ realPoint p ∈ support (R.route e) := by
  rw [← R.support_unitRoute e]
  exact mem_iff_realPoint_mem_support (fun _ he => subdivide_unit (R.route_orthogonal e) he) p

/-- Each original grid point occurs at most once in the actual traversal order. -/
theorem unitRoute_nodup (e : E) : (R.unitRoute e).Nodup :=
  subdivide_nodup (R.route_orthogonal e) (R.route_simple e)

/-- Each actual unit subdivision has one more point than the carrier's total Manhattan length.
-/
private theorem unitRoute_length (e : E) : (R.unitRoute e).length = wireLength (R.route e) + 1 := by
  rw [unitRoute, subdivide_length]
  simp only [route, PushPuzzle.NCL.Strip.Tracks.route, List.cons_ne_nil, ↓reduceIte]

/-- The actual unit traversal has a fixed length budget. -/
theorem unitRoute_length_le (e : E) : (R.unitRoute e).length ≤ routeBudget A K + 1 := by
  rw [R.unitRoute_length e]
  exact Nat.add_le_add_right (R.wireLength_route_le e) 1

/-- The fixed-budget subdivision program computes exactly the complete unit traversal. -/
theorem subdivideWithin_route_eq (e : E) :
    subdivideWithin (routeBudget A K) (R.route e) = R.unitRoute e :=
  subdivideWithin_eq_of_wireLength_le (R.route_orthogonal e) (R.wireLength_route_le e)

end PushPuzzle.NCL.Strip.Environment

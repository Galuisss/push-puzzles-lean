/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Slots
public import PushS.Source.Strip.Routes
import Mathlib.Tactic.Linarith

/-!
# Two-panel carriers on parity tracks

Each endpoint is in its owner's panel or the next panel. A vertex uses one fixed-capacity
slot in its panel. An edge uses one fixed-capacity slot in its owner panel and travels on the
track indexed by that slot and the owner's parity. Equal tracks in different owner panels have
disjoint full carrier windows.

## Main definitions

* `PushPuzzle.NCL.Strip.Environment`: geometric incidence data and its bounded row placements.
* `PushPuzzle.NCL.Strip.Environment.route`: the actual six-point carrier of each original edge.

## Main results

* `PushPuzzle.NCL.Strip.Environment.support_window`: full continuous support in two consecutive panels.
* `PushPuzzle.NCL.Strip.Environment.same_track_disjoint`: distinct same-track carriers are disjoint.
* `PushPuzzle.NCL.Strip.Environment.route_simple`: standard continuous simplicity for every carrier.
-/

public section

namespace PushPuzzle.NCL.Strip

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- Incidences and bounded panel placements used by the explicit fixed-track construction. -/
structure Environment (V E : Type*) (A K : ℕ) where
  /-- Vertex panel and slot data. -/
  vertices : Placement V A
  /-- Owner panel and slot data for each edge. -/
  edges : Placement E K
  /-- Endpoints in the original graph. -/
  endpoint : E → Bool → V
  /-- One of the three distinct local ports at each endpoint. -/
  port : E → Bool → Fin 3
  /-- The vertex and local port identify the entire incidence. -/
  incidence_injective : Function.Injective (fun p : E × Bool => (endpoint p.1 p.2, port p.1 p.2))
  /-- Original edges have distinct endpoint vertices. -/
  loopFree : ∀ e, endpoint e false ≠ endpoint e true
  /-- Both endpoint panels are among the owner's two consecutive panels. -/
  endpoint_rows : ∀ e d, edges.row e ≤ vertices.row (endpoint e d) ∧
    vertices.row (endpoint e d) ≤ edges.row e + 1

namespace Environment

open Cslib.Complexity Cslib.Complexity.NCL

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Track index combines the owner's parity with the edge's within-panel slot. -/
@[expose] def track (e : E) : ℕ := K * (R.edges.row e % 2) + R.edges.slot e

/-- Every actual track is among the fixed `2K` tracks. -/
private theorem track_lt (e : E) : R.track e < 2 * K := by
  have hs := (R.edges.slot e).isLt
  have hp := Nat.mod_lt (R.edges.row e) (by decide : 0 < 2)
  simp only [track]
  nlinarith

/-- Position of an original vertex in the strip. -/
@[expose] def center (v : V) : Point := PushPuzzle.NCL.Strip.Tracks.center (R.vertices.address v)

/-- Distinct source vertices occupy distinct actual strip centers. -/
theorem center_injective : Function.Injective R.center := by
  intro v w h
  apply R.vertices.address_injective
  have hx := congrArg Prod.fst h
  simp only [center, PushPuzzle.NCL.Strip.Tracks.center] at hx
  omega

/-- Actual carrier of one original edge, retaining its two original endpoint ports. -/
@[expose] def route (e : E) : Route :=
  PushPuzzle.NCL.Strip.Tracks.route (R.track e)
    (R.vertices.address (R.endpoint e false)) (R.vertices.address (R.endpoint e true))
    (R.port e false) (R.port e true)

private theorem address_window (e : E) (d : Bool) :
    8 * (A : ℤ) * R.edges.row e + 2 ≤
        8 * (R.vertices.address (R.endpoint e d) : ℤ) + 2 ∧
      8 * (R.vertices.address (R.endpoint e d) : ℤ) + 6 ≤
        8 * (A : ℤ) * (R.edges.row e + 2) - 2 := by
  have hr := R.endpoint_rows e d
  have hs := (R.vertices.slot (R.endpoint e d)).isLt
  simp only [PushPuzzle.NCL.Strip.Placement.address, Nat.cast_add, Nat.cast_mul]
  constructor <;> nlinarith

/-- All six listed points are strictly inside the owner's two-panel horizontal window.
The vertical side depends only on the fixed track capacity. -/
theorem point_window (e : E) {p : Point} (hp : p ∈ R.route e) :
    8 * (A : ℤ) * R.edges.row e + 2 ≤ p.1 ∧
      p.1 ≤ 8 * (A : ℤ) * (R.edges.row e + 2) - 2 ∧
      4 ≤ p.2 ∧ p.2 ≤ 4 * (K : ℤ) + 8 := by
  have h := PushPuzzle.NCL.Strip.Tracks.point_bounds (R.track_lt e) (R.address_window e false)
    (R.address_window e true) (R.port e false) (R.port e true) hp
  simpa only [Nat.cast_mul, Nat.cast_ofNat, ← mul_assoc, Int.reduceMul] using h

/-- Every real point of the complete carrier is in the same two-panel window. -/
theorem support_window (e : E) {p : ℝ × ℝ} (hp : p ∈ support (R.route e)) :
    8 * (A : ℝ) * R.edges.row e + 2 ≤ p.1 ∧
      p.1 ≤ 8 * (A : ℝ) * (R.edges.row e + 2) - 2 ∧
      4 ≤ p.2 ∧ p.2 ≤ 4 * (K : ℝ) + 8 := by
  have h := support_bounds_of_points (fun q hq => R.point_window e hq) hp
  simpa only [Int.cast_add, Int.cast_mul, Int.cast_sub, Int.cast_natCast, Int.cast_ofNat] using h

/-- Owners two or more panels apart have disjoint complete carrier supports. -/
private theorem separated_disjoint {e f : E} (hef : R.edges.row e + 2 ≤ R.edges.row f) :
    Disjoint (support (R.route e)) (support (R.route f)) := by
  rw [Set.disjoint_left]
  intro p hp hq
  have he := R.support_window e hp
  have hf := R.support_window f hq
  have hd : (R.edges.row e : ℝ) + 2 ≤ R.edges.row f := by exact_mod_cast hef
  have hA : (0 : ℝ) ≤ A := by positivity
  nlinarith

/-- Two distinct edges using the same track have owner panels of the same parity. -/
private theorem same_track_rows {e f : E} (h : R.track e = R.track f) :
    R.edges.row e % 2 = R.edges.row f % 2 := by
  have he := (R.edges.slot e).isLt
  have hf := (R.edges.slot f).isLt
  have hpe := Nat.mod_lt (R.edges.row e) (by decide : 0 < 2)
  have hpf := Nat.mod_lt (R.edges.row f) (by decide : 0 < 2)
  simp only [track] at h
  nlinarith

/-- Equal-height carriers of different edges are separated by a full panel boundary margin. -/
theorem same_track_disjoint {e f : E} (hef : e ≠ f) (h : R.track e = R.track f) :
    Disjoint (support (R.route e)) (support (R.route f)) := by
  have hp := R.same_track_rows h
  have hr : R.edges.row e ≠ R.edges.row f := by
    intro hr
    apply hef
    apply R.edges.injective
    apply Prod.ext hr
    apply Fin.ext
    change (R.edges.slot e).val = (R.edges.slot f).val
    simp only [track, hr] at h
    omega
  rcases lt_or_gt_of_ne hr with hr | hr
  · exact R.separated_disjoint (by omega)
  · exact (R.separated_disjoint (by omega)).symm

/-- Every actual carrier has five proper orthogonal segments. -/
theorem route_orthogonal (e : E) : IsOrthogonal (R.route e) :=
  PushPuzzle.NCL.Strip.Tracks.route_orthogonal (fun h => R.loopFree e (R.vertices.address_injective h)) _ _

/-- Every actual carrier is continuously simple. -/
theorem route_simple (e : E) : IsSimple (R.route e) :=
  PushPuzzle.NCL.Strip.Tracks.route_simple (fun h => R.loopFree e (R.vertices.address_injective h)) _ _

/-- The actual carrier encounters exactly its two original vertex centers. -/
theorem center_mem_support_iff (e : E) (v : V) :
    realPoint (R.center v) ∈ support (R.route e) ↔
      v = R.endpoint e false ∨ v = R.endpoint e true := by
  rw [center, route, PushPuzzle.NCL.Strip.Tracks.center_mem_support_iff]
  simp only [Function.Injective.eq_iff R.vertices.address_injective]

end Environment
end PushPuzzle.NCL.Strip

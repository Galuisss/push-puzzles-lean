/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Basic
public import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual grid-panel feature density

Distinct paths meet only at a common incident vertex. A three-port graph therefore has at most
three path incidences at any grid point. A bounded-width row has only a fixed number of grid
points, bounding all actual edge-point features on that row. Vertex row separation gives at
most one actual vertex per row.

## Main definitions

* `PushPuzzle.NCL.GridDrawing.RowFeature`: an actual edge-point feature in one bounded-width grid row.

## Main results

* `PushPuzzle.NCL.GridDrawing.Closed.point_edges_le`: at most three edges pass through one actual grid point.
* `PushPuzzle.NCL.GridDrawing.Closed.row_features_le`: bounded-width rows contain bounded actual path features.
* `PushPuzzle.NCL.GridDrawing.Closed.panel_vertices_le`: each unit-height panel has at most one actual vertex.
-/

public section

namespace PushPuzzle.NCL.GridDrawing

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib GridRouting

open scoped BigOperators

variable {V E : Type*} {G : ConstraintGraph V E} (P : Closed G)

/-- An actual edge and an actual grid point in one bounded-width drawing row. -/
structure RowFeature (width row : ℕ) where
  /-- Column of the actual grid point. -/
  column : Fin (width + 1)
  /-- Actual graph edge through that point. -/
  edge : E
  /-- The point lies on that edge's complete actual path. -/
  on_path : (P.path edge).Contains (column.val, row)

instance [Finite E] (width row : ℕ) : Finite (RowFeature P width row) :=
  Finite.of_injective (fun f : RowFeature P width row => (f.column, f.edge)) (by
    rintro ⟨x, e, h⟩ ⟨x', e', h'⟩ he
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
    rfl)

/-- At most three actual paths pass through any grid point of a three-port graph drawing. -/
theorem Closed.point_edges_le [Finite E] (hports : ∀ v, (G v).ports.length ≤ 3) (p : Point) :
    Nat.card {e // (P.path e).Contains p} ≤ 3 := by
  classical
  let := Fintype.ofFinite E
  let es := Finset.univ.filter (fun e => (P.path e).Contains p)
  change Nat.card {e // (P.path e).Contains p} ≤ _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  change es.card ≤ 3
  by_cases hs : es.card ≤ 1
  · omega
  obtain ⟨e, f, he, hf, hef⟩ := Finset.one_lt_card_iff.mp (show 1 < es.card by omega)
  have heP := (Finset.mem_filter.mp he).2
  have hfP := (Finset.mem_filter.mp hf).2
  obtain ⟨v, hv, hev, _⟩ := P.meet e f p hef heP hfP
  have hsub : es ⊆ ((G v).ports.map (fun q => q.1.edge)).toFinset := by
    intro g hg
    have hgv : Incident G v g := by
      by_cases hge : g = e
      · exact hge ▸ hev
      · obtain ⟨v', hv', _, hgv'⟩ := P.meet e g p (Ne.symm hge) heP (Finset.mem_filter.mp hg).2
        have hveq : v' = v := P.vertex_injective (hv'.symm.trans hv)
        exact hveq ▸ hgv'
    obtain ⟨d, weight, hweight⟩ := hgv
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨⟨⟨g, d⟩, weight⟩, hweight, rfl⟩)
  have hc := (Finset.card_le_card hsub).trans (List.toFinset_card_le _)
  exact hc.trans (by simpa only [List.length_map] using hports v)

private def rowFeatureEquiv (width row : ℕ) :
    RowFeature P width row ≃ (Σ x : Fin (width + 1), {e // (P.path e).Contains (x.val, row)}) where
  toFun f := ⟨f.column, f.edge, f.on_path⟩
  invFun f := ⟨f.1, f.2.1, f.2.2⟩
  left_inv f := by cases f; rfl
  right_inv f := by rcases f with ⟨x, e, h⟩; rfl

/-- Each actual bounded-width row contains only a fixed number of actual edge-point features. -/
theorem Closed.row_features_le [Finite E] (hports : ∀ v, (G v).ports.length ≤ 3)
    (width row : ℕ) : Nat.card (RowFeature P width row) ≤ 3 * (width + 1) := by
  classical
  let := Fintype.ofFinite E
  rw [Nat.card_congr (rowFeatureEquiv P width row)]
  have hs : Nat.card (Σ x : Fin (width + 1), {e // (P.path e).Contains (x.val, row)}) =
      ∑ x : Fin (width + 1), Nat.card {e // (P.path e).Contains (x.val, row)} := by
    simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]
  rw [hs]
  calc
    _ ≤ ∑ _x : Fin (width + 1), 3 := Finset.sum_le_sum (fun _ _ => (PushPuzzle.NCL.GridDrawing.Closed.point_edges_le P) hports _)
    _ = 3 * (width + 1) := by simp [Nat.mul_comm]

/-- Vertex row separation permits at most one actual vertex in each closed unit-height panel. -/
theorem Closed.panel_vertices_le (panel : ℕ) :
    Nat.card {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} ≤ 1 := by
  have : Subsingleton {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} := ⟨by
    intro v w
    apply Subtype.ext
    by_contra hne
    have h := P.vertex_separation v.1 w.1 hne
    have hv := v.2
    have hw := w.2
    omega⟩
  simpa only [Nat.card_unique] using Nat.card_le_card_of_injective
    (fun _ : {v // panel ≤ (P.vertex v).2 ∧ (P.vertex v).2 ≤ panel + 1} => ())
    (fun _ _ _ => Subsingleton.elim _ _)

end PushPuzzle.NCL.GridDrawing

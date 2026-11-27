/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.PanelDensity
public import PushS.Source.Planar.GridDrawing.UnitRoute
import all PushS.Source.Planar.GridDrawing.UnitRoute
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute
import Mathlib.Data.Fintype.Sigma
import Mathlib.Basic.Finite.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Actual unit-route feature counts in a strip panel

Cycle-erased unit routes retain only points of their complete paths. Distinct entries of one
route have distinct grid points. Thus actual route visits in one row inject into its bounded
edge-point features; the two integer rows of a unit-height panel have a fixed total budget.

## Main definitions

* `PushPuzzle.NCL.GridDrawing.RouteVisit`: an actual listed unit-route entry on one row.
* `PushPuzzle.NCL.GridDrawing.PanelVisit`: an actual listed entry on either boundary row of one unit panel.

## Main results

* `PushPuzzle.NCL.GridDrawing.Closed.row_visits_le`: fixed bound on actual listed route entries per row.
* `PushPuzzle.NCL.GridDrawing.Closed.panel_visits_le`: fixed bound on all actual listed entries per unit panel.
-/

public section

namespace PushPuzzle.NCL.GridDrawing

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib GridRouting

open scoped BigOperators

variable {V E : Type*} {G : ConstraintGraph V E} (P : Closed G)

/-- An actual listed point of an actual edge's normalized unit route on one grid row. -/
structure RouteVisit (row : ℕ) where
  /-- The original edge of the actual listed route. -/
  edge : E
  /-- Its actual position in the cycle-erased unit route. -/
  index : Fin (P.path edge).unitRoute.length
  /-- The listed point's nonnegative row is the specified row. -/
  at_row : (((P.path edge).unitRoute.get index).2).toNat = row

instance [Finite E] (row : ℕ) : Finite (RouteVisit P row) :=
  Finite.of_injective
    (fun f : RouteVisit P row => (⟨f.edge, f.index⟩ : Σ e, Fin (P.path e).unitRoute.length)) (by
      rintro ⟨e, i, h⟩ ⟨e', i', h'⟩ he
      cases he
      rfl)

namespace RouteVisit

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing

/-- The nonnegative grid point of the actual listed unit-route entry. -/
@[expose] def point {row : ℕ} (f : RouteVisit P row) : GridRouting.Point :=
  let p := (P.path f.edge).unitRoute.get f.index
  (p.1.toNat, p.2.toNat)

/-- This actual grid point is the original listed integer point and belongs to the full path. -/
theorem point_spec {row : ℕ} (f : RouteVisit P row) :
    integerPoint (f.point P) = (P.path f.edge).unitRoute.get f.index ∧
      (P.path f.edge).Contains (f.point P) := by
  obtain ⟨p, hp, hm⟩ := (P.path f.edge).unitRoute_trace _ (List.get_mem _ f.index)
  have he : f.point P = p := by
    dsimp only [point]
    rw [← hp]
    simp [integerPoint]
  exact ⟨(congrArg integerPoint he).trans hp, he.symm ▸ hm⟩

/-- Read an actual listed unit-route entry as the corresponding actual row feature. -/
@[expose] def toFeature {width row : ℕ}
    (hW : ∀ e p, (P.path e).Contains p → p.1 ≤ width) (f : RouteVisit P row) :
    RowFeature P width row where
  column := ⟨(f.point P).1, by have h := hW _ _ (f.point_spec P).2; omega⟩
  edge := f.edge
  on_path := by
    have h := (f.point_spec P).2
    have hr : (f.point P).2 = row := f.at_row
    exact (Prod.ext rfl hr : f.point P = ((f.point P).1, row)) ▸ h

/-- Actual unit-route positions give distinct actual edge-point features. -/
private theorem toFeature_injective {width row : ℕ}
    (hW : ∀ e p, (P.path e).Contains p → p.1 ≤ width) :
    Function.Injective (toFeature P (row := row) hW) := by
  rintro ⟨e, i, hi⟩ ⟨f, j, hj⟩ h
  have he := congrArg PushPuzzle.NCL.GridDrawing.RowFeature.edge h
  change e = f at he
  subst f
  have hx := congrArg (fun f : RowFeature P width row => f.column.val) h
  have hpoint : point P ⟨e, i, hi⟩ = point P ⟨e, j, hj⟩ :=
    Prod.ext hx (hi.trans hj.symm)
  have hget := (point_spec P (⟨e, i, hi⟩ : RouteVisit P row)).1.symm.trans
    ((congrArg integerPoint hpoint).trans (point_spec P (⟨e, j, hj⟩ : RouteVisit P row)).1)
  have hij := (List.nodup_iff_injective_get.mp (P.path e).unitRoute_nodup) hget
  cases hij
  rfl

end RouteVisit

/-- Actual listed unit-route features on either integer boundary row of one unit-height panel.
-/
structure PanelVisit (panel : ℕ) where
  /-- Lower or upper integer row of this panel. -/
  side : Fin 2
  /-- The actual listed unit-route entry on that actual row. -/
  visit : RouteVisit P (panel + side.val)

instance [Finite E] (panel : ℕ) : Finite (PanelVisit P panel) :=
  Finite.of_injective
    (fun f : PanelVisit P panel =>
      (⟨f.side, f.visit⟩ : Σ side : Fin 2, RouteVisit P (panel + side.val)))
    (by rintro ⟨s, v⟩ ⟨s', v'⟩ h; cases h; rfl)

/-- Each bounded row contains a fixed number of actual normalized-route entries. -/
theorem Closed.row_visits_le [Finite E] (hports : ∀ v, (G v).ports.length ≤ 3) (width row : ℕ)
    (hW : ∀ e p, (P.path e).Contains p → p.1 ≤ width) :
    Nat.card (RouteVisit P row) ≤ 3 * (width + 1) :=
  (Nat.card_le_card_of_injective (PushPuzzle.NCL.GridDrawing.RouteVisit.toFeature P hW)
    (PushPuzzle.NCL.GridDrawing.RouteVisit.toFeature_injective P hW)).trans (PushPuzzle.NCL.GridDrawing.Closed.row_features_le P hports width row)

/-- Unit-height panels contain a fixed number of actual listed route features, including bends.
-/
theorem Closed.panel_visits_le [Finite E] (hports : ∀ v, (G v).ports.length ≤ 3) (width panel : ℕ)
    (hW : ∀ e p, (P.path e).Contains p → p.1 ≤ width) :
    Nat.card (PanelVisit P panel) ≤ 6 * (width + 1) := by
  let feature (f : PanelVisit P panel) :
      Σ side : Fin 2, RowFeature P width (panel + side.val) :=
    ⟨f.side, PushPuzzle.NCL.GridDrawing.RouteVisit.toFeature P hW f.visit⟩
  have hinj : Function.Injective feature := by
    rintro ⟨s, f⟩ ⟨t, g⟩ h
    have hst := congrArg Sigma.fst h
    change s = t at hst
    subst t
    have hv := eq_of_heq (Sigma.mk.inj h).2
    have hfg := PushPuzzle.NCL.GridDrawing.RouteVisit.toFeature_injective P hW hv
    cases hfg
    rfl
  have hc := Nat.card_le_card_of_injective feature hinj
  have hs : Nat.card (Σ side : Fin 2, RowFeature P width (panel + side.val)) ≤
      6 * (width + 1) := by
    rw [Nat.card_sigma]
    calc
      _ ≤ ∑ _side : Fin 2, 3 * (width + 1) :=
        Finset.sum_le_sum (fun _ _ => PushPuzzle.NCL.GridDrawing.Closed.row_features_le P hports width _)
      _ = 6 * (width + 1) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_id]
        omega
  exact hc.trans hs

end PushPuzzle.NCL.GridDrawing

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.RouteDensity
import PushS.Source.Orthogonal.UnitSegments
import Mathlib.Tactic.Linarith

import all CslibFrontier.Foundations.Geometry.Orthogonal.UnitSegments

/-!
# Actual unit-edge pieces in one strip panel

Each actual unit-route segment touching a unit-height panel has an endpoint on one of the
panel's two integer rows. Select such an actual route visit and record whether it is the first
or second endpoint. This injects actual segment positions into twice the actual visit budget.

## Main definitions

* `PushPuzzle.NCL.GridDrawing.PanelSegment`: an actual listed unit segment with an endpoint in one strip panel.

## Main results

* `PushPuzzle.NCL.GridDrawing.Closed.panel_segments_le`: fixed bound on actual listed unit-edge pieces per panel.
-/

public section

namespace PushPuzzle.NCL.GridDrawing

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib

variable {V E : Type*} {G : ConstraintGraph V E} (P : Closed G)

/-- An actual listed unit-route segment with at least one endpoint in a closed unit-height panel.
-/
structure PanelSegment (panel : ℕ) where
  /-- Actual graph edge carrying the segment. -/
  edge : E
  /-- Actual position in that edge's consecutive unit-segment list. -/
  index : Fin (P.path edge).unitRoute.consecutivePairs.length
  /-- At least one actual endpoint is in the panel. -/
  touch :
    let s := (P.path edge).unitRoute.consecutivePairs.get index
    let first := s.1
    let second := s.2
    (panel ≤ first.2.toNat ∧ first.2.toNat ≤ panel + 1) ∨
      (panel ≤ second.2.toNat ∧ second.2.toNat ≤ panel + 1)

namespace PanelSegment

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing

private theorem index_succ_lt {panel : ℕ} (f : PanelSegment P panel) :
    f.index.val + 1 < (P.path f.edge).unitRoute.length := by
  have h := f.index.isLt
  simp only [List.consecutivePairs, List.length_zip, List.length_tail] at h
  omega

private theorem pair_at_index {panel : ℕ} (f : PanelSegment P panel) :
    (P.path f.edge).unitRoute.consecutivePairs.get f.index =
      ((P.path f.edge).unitRoute[f.index.val]'(by have := index_succ_lt P f; omega),
        (P.path f.edge).unitRoute[f.index.val + 1]'(index_succ_lt P f)) := by
  simp only [List.get_eq_getElem, List.consecutivePairs, List.getElem_zip, List.getElem_tail]

/-- The constructed actual endpoint visit, with its actual original edge and segment index. -/
structure Endpoint {panel : ℕ} (f : PanelSegment P panel) where
  /-- The selected actual listed endpoint on the panel. -/
  visit : PanelVisit P panel
  /-- Whether the selected endpoint is the second endpoint of the actual segment. -/
  second : Bool
  /-- The actual edge is retained. -/
  edge_eq : visit.visit.edge = f.edge
  /-- The actual route index is the original segment index plus the endpoint flag. -/
  index_eq : visit.visit.index.val = f.index.val + if second then 1 else 0

/-- Select an actual endpoint visit and retain its checked actual position metadata. -/
@[expose] def endpoint {panel : ℕ} (f : PanelSegment P panel) : Endpoint P f :=
  let first := ((P.path f.edge).unitRoute.consecutivePairs.get f.index).1
  if h : panel ≤ first.2.toNat ∧ first.2.toNat ≤ panel + 1 then
    { visit := ⟨⟨((P.path f.edge).unitRoute[f.index.val]'(by
      have := index_succ_lt P f; omega)).2.toNat - panel,
      by
        have hh := pair_at_index P f
        dsimp only [first] at h
        rw [hh] at h
        dsimp only at h
        omega⟩,
      ⟨f.edge, ⟨f.index.val, by have := index_succ_lt P f; omega⟩, by
        have hh := pair_at_index P f
        dsimp only [first] at h
        rw [hh] at h
        dsimp only at h ⊢
        simp only [List.get_eq_getElem]
        omega⟩⟩
      second := false
      edge_eq := rfl
      index_eq := by simp }
  else
    { visit := ⟨⟨((P.path f.edge).unitRoute[f.index.val + 1]'(by
        exact index_succ_lt P f)).2.toNat - panel,
      by
        have hh := pair_at_index P f
        have ht := f.touch.resolve_left h
        rw [hh] at ht
        dsimp only at ht
        omega⟩,
      ⟨f.edge, ⟨f.index.val + 1, by exact index_succ_lt P f⟩, by
        have hh := pair_at_index P f
        have ht := f.touch.resolve_left h
        rw [hh] at ht
        dsimp only at ht ⊢
        simp only [List.get_eq_getElem]
        omega⟩⟩
      second := true
      edge_eq := rfl
      index_eq := rfl }

/-- The selected actual panel visit and endpoint flag, used for the finite feature count. -/
@[expose] def toVisit {panel : ℕ} (f : PanelSegment P panel) : PanelVisit P panel × Bool :=
  ((f.endpoint P).visit, (f.endpoint P).second)

private theorem toVisit_edge {panel : ℕ} (f : PanelSegment P panel) :
    (f.toVisit P).1.visit.edge = f.edge := (f.endpoint P).edge_eq

private theorem toVisit_index {panel : ℕ} (f : PanelSegment P panel) :
    (f.toVisit P).1.visit.index.val = f.index.val + if (f.toVisit P).2 then 1 else 0 :=
  (f.endpoint P).index_eq

/-- The selected actual visit and endpoint flag identify the actual original unit-segment index.
-/
private theorem toVisit_injective {panel : ℕ} : Function.Injective (toVisit P
    (panel := panel)) := by
  rintro ⟨e, i, hi⟩ ⟨f, j, hj⟩ h
  have he := (toVisit_edge P (⟨e, i, hi⟩ : PanelSegment P panel)).symm.trans
    ((congrArg (fun x : PanelVisit P panel × Bool => x.1.visit.edge) h).trans
      (toVisit_edge P (⟨f, j, hj⟩ : PanelSegment P panel)))
  change e = f at he
  subst f
  have hidx := congrArg (fun x : PanelVisit P panel × Bool => x.1.visit.index.val) h
  have hside := congrArg Prod.snd h
  rw [toVisit_index, toVisit_index] at hidx
  dsimp only at hidx
  have hij : i = j := Fin.ext (by rw [hside] at hidx; omega)
  cases hij
  rfl

end PanelSegment

/-- The actual unit-edge pieces per panel have twice the fixed actual listed-visit budget. -/
theorem Closed.panel_segments_le [Finite E] (hports : ∀ v, (G v).ports.length ≤ 3)
    (width panel : ℕ) (hW : ∀ e p, (P.path e).Contains p → p.1 ≤ width) :
    Nat.card (PanelSegment P panel) ≤ 12 * (width + 1) := by
  have hc := Nat.card_le_card_of_injective (PushPuzzle.NCL.GridDrawing.PanelSegment.toVisit P (panel := panel))
    (PushPuzzle.NCL.GridDrawing.PanelSegment.toVisit_injective P)
  have hb : Nat.card Bool = 2 := by rw [Nat.card_eq_fintype_card]; decide
  rw [Nat.card_prod, hb] at hc
  have hv := (PushPuzzle.NCL.GridDrawing.Closed.panel_visits_le P) hports width panel hW
  omega

end PushPuzzle.NCL.GridDrawing

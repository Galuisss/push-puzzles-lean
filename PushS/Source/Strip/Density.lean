/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Environment
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

/-!
# Constant feature budgets in each strip panel

A carrier meeting panel `r` is owned by panel `r` or its predecessor. Its owner's slot and one
parity bit therefore identify it among at most `2K` carriers. Counting all six listed points and
all five segments of every such carrier gives a uniform conservative feature budget.

## Main definitions

* `PushPuzzle.NCL.Strip.Environment.panel`: the full closed longitudinal panel.
* `PushPuzzle.NCL.Strip.Environment.CarrierFeature`: actual listed-point and segment occurrences.
* `PushPuzzle.NCL.Strip.Environment.MeetsPanel`: the actual continuous carrier meets that panel.

## Main results

* `PushPuzzle.NCL.Strip.Environment.meetsPanel_card_le`: at most `2K` original carriers per panel.
* `PushPuzzle.NCL.Strip.Environment.panel_features_le`: vertex, listed-point, and segment budget `A + 22K`.
-/

public section

namespace PushPuzzle.NCL.Strip.Environment

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- A longitudinal panel, including its two vertical boundary lines. -/
@[expose] def panel (A r : ℕ) : Set (ℝ × ℝ) :=
  {p | 8 * (A : ℝ) * r ≤ p.1 ∧ p.1 ≤ 8 * (A : ℝ) * (r + 1)}

/-- The whole continuous carrier has a real point in the specified panel. -/
@[expose] def MeetsPanel (r : ℕ) (e : E) : Prop :=
  ∃ p ∈ support (R.route e), p ∈ panel A r

private theorem owner_of_meetsPanel {r : ℕ} {e : E} (h : R.MeetsPanel r e) :
    R.edges.row e = r ∨ R.edges.row e + 1 = r := by
  obtain ⟨p, hp, hr⟩ := h
  have hw := R.support_window e hp
  have hA : (0 : ℝ) ≤ A := by positivity
  have hr₀ : R.edges.row e ≤ r := by
    by_contra hh
    have hh' : (r : ℝ) + 1 ≤ R.edges.row e := by
      exact_mod_cast (show r + 1 ≤ R.edges.row e by omega)
    have hp' := hr.2
    nlinarith
  have hr₁ : r ≤ R.edges.row e + 1 := by
    by_contra hh
    have hh' : (R.edges.row e : ℝ) + 2 ≤ r := by
      exact_mod_cast (show R.edges.row e + 2 ≤ r by omega)
    have hp' := hr.1
    nlinarith
  omega

/-- At most twice the fixed edge-slot budget of original carriers meet any given panel. -/
theorem meetsPanel_card_le (r : ℕ) : Nat.card {e // R.MeetsPanel r e} ≤ 2 * K := by
  classical
  let f : {e // R.MeetsPanel r e} → Bool × Fin K :=
    fun e => (decide (R.edges.row e.val = r), R.edges.slot e.val)
  have hf : Function.Injective f := by
    intro e f' hh
    have he := R.owner_of_meetsPanel e.property
    have hf' := R.owner_of_meetsPanel f'.property
    have hr : R.edges.row e.val = R.edges.row f'.val := by
      have hb : (R.edges.row e.val = r ↔ R.edges.row f'.val = r) :=
        decide_eq_decide.mp (congrArg (fun x : Bool × Fin K => x.1) hh)
      by_cases h : R.edges.row e.val = r
      · exact h.trans (hb.mp h).symm
      · have h' : R.edges.row f'.val ≠ r := fun h' => h (hb.mpr h')
        omega
    apply Subtype.ext
    apply R.edges.injective
    apply Prod.ext hr
    exact congrArg (fun x : Bool × Fin K => x.2) hh
  have hh := Nat.card_le_card_of_injective f hf
  simpa only [Nat.card_prod, Nat.card_eq_fintype_card, Fintype.card_prod,
    Fintype.card_bool, Fintype.card_fin] using hh

/-- Listed-point and segment occurrences of carriers whose full real support meets the panel.
The two summands use the actual route length and actual consecutive-segment count. -/
@[expose] def CarrierFeature (r : ℕ) : Type _ :=
  Σ e : {e // R.MeetsPanel r e},
    Fin (R.route e.val).length ⊕ Fin (R.route e.val).consecutivePairs.length

/-- Original vertices and actual listed-point/segment occurrences of every carrier meeting
one panel have a constant total budget. -/
theorem panel_features_le (r : ℕ) :
    Nat.card {v // R.vertices.row v = r} + Nat.card (R.CarrierFeature r) ≤ A + 22 * K := by
  have hv := R.vertices.card_row_le r
  have he := R.meetsPanel_card_le r
  have hc : Nat.card (R.CarrierFeature r) = 11 * Nat.card {e // R.MeetsPanel r e} := by
    change Nat.card (Σ _ : {e // R.MeetsPanel r e}, Fin 6 ⊕ Fin 5) = _
    rw [Nat.card_congr (Equiv.sigmaEquivProd _ _), Nat.card_prod]
    simp only [Nat.card_sum, Nat.card_fin]
    omega
  omega

end PushPuzzle.NCL.Strip.Environment

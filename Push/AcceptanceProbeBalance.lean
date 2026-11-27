/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Finset.Card

/-! Row inventory balance forces every ordinary and middle probe to pay its exact canonical count. -/

public section
namespace PushPuzzle.Push.AcceptanceProbeBalance

open scoped BigOperators

variable {ι : Type} [Fintype ι]

/-- Literal local probe inventories and exact per-level row totals. -/
structure Conditions (level : ι → ℕ) (Middle : ι → Prop) (target observed J D : ι → ℕ)
    [DecidablePred Middle] : Prop where
  middle_even : ∀ i, Middle i → level i % 2 = 0
  ordinary_even_zero : ∀ i, ¬Middle i → level i % 2 = 0 → J i = 0
  ordinary_balance : ∀ i, ¬Middle i → J i + observed i = target i
  middle_balance : ∀ i, Middle i → target i + D i ≤ observed i
  row_balance : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => level i = j), observed i =
    ∑ i ∈ Finset.univ.filter (fun i => level i = j), target i

namespace Conditions

variable {level : ι → ℕ} {Middle : ι → Prop} [DecidablePred Middle]
  {target observed J D : ι → ℕ} (h : Conditions level Middle target observed J D)

include h

private theorem odd_le {j : ℕ} (hj : j % 2 ≠ 0) (i : ι) (hi : level i = j) : observed i ≤ target i := by
  have hm : ¬Middle i := fun hm => hj (hi ▸ h.middle_even i hm)
  have hb := h.ordinary_balance i hm
  omega

private theorem even_le {j : ℕ} (hj : j % 2 = 0) (i : ι) (hi : level i = j) : target i ≤ observed i := by
  by_cases hm : Middle i
  · have hb := h.middle_balance i hm
    omega
  · have hz := h.ordinary_even_zero i hm (hi ▸ hj)
    have hb := h.ordinary_balance i hm
    omega

/-- Equal row totals turn the parity-directed local inequalities into exact individual probe counts. -/
private theorem observed_eq_target (i : ι) : observed i = target i := by
  let row := Finset.univ.filter fun k => level k = level i
  have hi : i ∈ row := Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl⟩
  by_cases hj : level i % 2 = 0
  · have he := (Finset.sum_eq_sum_iff_of_le (fun k hk =>
        h.even_le hj k (Finset.mem_filter.mp hk).2)).mp (h.row_balance (level i)).symm
    exact (he i hi).symm
  · have he := (Finset.sum_eq_sum_iff_of_le (fun k hk =>
        h.odd_le hj k (Finset.mem_filter.mp hk).2)).mp (h.row_balance (level i))
    exact he i hi

/-- Every ordinary probe pays zero incoming surplus. -/
private theorem ordinary_J_zero (i : ι) (hm : ¬Middle i) : J i = 0 := by
  have hb := h.ordinary_balance i hm
  have he := h.observed_eq_target i
  omega

/-- Every middle probe pays zero deficit. -/
private theorem middle_D_zero (i : ι) (hm : Middle i) : D i = 0 := by
  have hb := h.middle_balance i hm
  have he := h.observed_eq_target i
  omega

/-- The complete finite probe certificate gives exact observed counts and vanishing local errors. -/
theorem exact (i : ι) : observed i = target i ∧ (¬Middle i → J i = 0) ∧ (Middle i → D i = 0) :=
  ⟨h.observed_eq_target i, h.ordinary_J_zero i, h.middle_D_zero i⟩

end Conditions
end PushPuzzle.Push.AcceptanceProbeBalance

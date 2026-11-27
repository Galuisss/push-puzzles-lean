/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProbePartners
public import Push.AcceptanceProbeBalance

/-! Actual repaired probe levels cancel all signed ordinary-axis surplus and gate-axis deficit. -/

public section
namespace PushPuzzle.Push.AcceptanceProbe

open PushS PushS.PortLayout
open scoped BigOperators

/-- Repaired partner geometry and exact real probe-row totals eliminate every local inventory error. -/
theorem cancel (l : PortLayout) (hl : l.pages.Valid) (hpartners : Partner.ReaderPartners l)
    (target observed J D : Fin l.portCount → ℕ)
    (hwire : ∀ i, Partner.Ordinary l i.val → J i = 0)
    (hordinary : ∀ i, ¬Partner.Middle l i.val → J i + observed i = target i)
    (hmiddle : ∀ i, Partner.Middle l i.val → target i + D i ≤ observed i)
    (hrows : ∀ j, ∑ i ∈ Finset.univ.filter (fun i => level l hl i = j), observed i =
      ∑ i ∈ Finset.univ.filter (fun i => level l hl i = j), target i) (i : Fin l.portCount) :
    observed i = target i ∧ (¬Partner.Middle l i.val → J i = 0) ∧ (Partner.Middle l i.val → D i = 0) := by
  classical
  have h : AcceptanceProbeBalance.Conditions (level l hl) (fun i => Partner.Middle l i.val)
      target observed J D := {
    middle_even := level_middle_even l hl
    ordinary_even_zero i hm heven := hwire i (level_even_wire l hl hpartners i heven hm)
    ordinary_balance := hordinary
    middle_balance := hmiddle
    row_balance := hrows }
  exact h.exact i

end PushPuzzle.Push.AcceptanceProbe

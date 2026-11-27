/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerCutsPaths
public import CslibFrontier.Foundations.Data.List.OfFn

/-! Literal interval loads and the standard finite page-depth budgets. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

/-- Test whether an arc crosses the gap after the numbered port. -/
def gapTest (gap : ℕ) (ab : ℕ × ℕ) : Bool := decide (ab.1 ≤ gap ∧ gap < ab.2)

/-- Actual upper arcs crossing one port gap. -/
def upperLoad (l : PortLayout) (gap : ℕ) : ℕ := l.upperPairs.countP (gapTest gap)

/-- Actual lower WIRE and gate intervals crossing one port gap. -/
def lowerLoad (l : PortLayout) (gap : ℕ) : ℕ :=
  l.lowerGroups.countP fun g => gapTest gap (g.shape.left, g.shape.right)

private theorem active_card_countP (p : Page) (gap : ℕ) :
    (p.active gap).card = p.groups.countP (fun g => decide (g.left ≤ gap ∧ gap < g.right)) := by
  rw [List.countP_eq_card_filter_getElem]
  congr 1

private theorem upperLoad_eq_active (l : PortLayout) (gap : ℕ) :
    upperLoad l gap = (l.pages.upperPage.active gap).card := by
  rw [active_card_countP]
  simp only [upperLoad, PortLayout.pages, Pages.upperPage, List.countP_map, Function.comp_def, Group.left, Group.right]
  rfl

private theorem lowerLoad_eq_active (l : PortLayout) (gap : ℕ) :
    lowerLoad l gap = (l.pages.lowerPage.active gap).card := by
  rw [active_card_countP]
  simp only [lowerLoad, PortLayout.pages, Pages.lowerPage, List.countP_map, Function.comp_def, gapTest]

private theorem active_card_le_maxActive {p : Page} (hp : p.Valid) (gap : ℕ) :
    (p.active gap).card ≤ p.maxActive := by
  by_cases hgap : gap < p.portCount - 1
  · exact Finset.le_sup (f := fun k => (p.active k).card) (Finset.mem_range.mpr hgap)
  · have he : p.active gap = ∅ := by
      ext i
      simp only [Page.active, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty,
        iff_false, not_and]
      have hb := hp.bounded i
      omega
    rw [he, Finset.card_empty]
    exact Nat.zero_le _

theorem upperLoad_le_maxActive {l : PortLayout} (hl : l.pages.Valid) (gap : ℕ) :
    upperLoad l gap ≤ l.pages.upperPage.maxActive := by
  rw [upperLoad_eq_active]
  exact active_card_le_maxActive hl.upper gap

theorem lowerLoad_le_maxActive {l : PortLayout} (hl : l.pages.Valid) (gap : ℕ) :
    lowerLoad l gap ≤ l.pages.lowerPage.maxActive := by
  rw [lowerLoad_eq_active]
  exact active_card_le_maxActive hl.lower gap

theorem upper_maxActive_le {l : PortLayout} {bound : ℕ} (hload : ∀ gap, upperLoad l gap ≤ bound) :
    l.pages.upperPage.maxActive ≤ bound := by
  apply Finset.sup_le
  intro gap _
  rw [← upperLoad_eq_active]
  exact hload gap

theorem lower_maxActive_le {l : PortLayout} {bound : ℕ} (hload : ∀ gap, lowerLoad l gap ≤ bound) :
    l.pages.lowerPage.maxActive ≤ bound := by
  apply Finset.sup_le
  intro gap _
  rw [← lowerLoad_eq_active]
  exact hload gap

/-- The actual sorted crossing array has exactly the source upper load at its cut gap. -/
theorem cut_active_length (l : PortLayout) {cut : ℕ} (hc : 0 < cut) :
    (Cuts.active l cut).length = upperLoad l (cut - 1) := by
  rw [Cuts.active, (Comb.Sort.run_perm _ _ _).length_eq, ← List.countP_eq_length_filter]
  unfold upperLoad
  apply List.countP_congr
  intro ab _
  simp only [Cuts.crosses, gapTest, decide_eq_true_eq]
  omega

theorem cut_active_zero (l : PortLayout) : (Cuts.active l 0).length = 0 := by
  rw [Cuts.active, (Comb.Sort.run_perm _ _ _).length_eq]
  simp [Cuts.crosses]

end PushPuzzle.Push.Partner.Resources

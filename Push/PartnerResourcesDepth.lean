/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesEarLower
import all PushS.PageLevels
import Mathlib.Data.Finset.Max

/-! Constant repaired working-level budgets and linear size for bounded-depth sources. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS PageLevels

private def isWire : Group → Bool
  | .wire .. => true
  | .triple .. => false

private theorem lower_maxActive_le_highest {p : Pages} (hp : p.Valid) :
    p.lowerPage.maxActive ≤ p.highest := by
  let wires := Finset.univ.filter fun i : p.lowerPage.Index => isWire (p.lowerPage.group i)
  by_cases hn : wires.Nonempty
  · obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image wires (fun i => (p.lowerPage.ancestors i).card) hn
    have hw : isWire (p.lowerPage.group i) = true := (Finset.mem_filter.mp hi).2
    have hanc : p.lowerPage.ancestors i = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hc : (p.lowerPage.group j).Contains (p.lowerPage.group i) := (Finset.mem_filter.mp hj).2
      have hjw : j ∈ wires := by
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        cases he : p.lowerPage.group j with
        | wire a b => rfl
        | triple a => exact (Page.triple_leaf hp.lower he hc).elim
      have hsmall := hmin j hjw
      have hlt := Page.ancestors_card_lt hc
      omega
    have hlevel : p.lowerLevel i = p.lowerPage.maxActive + 1 := by
      cases he : p.lowerPage.group i with
      | triple a => simp only [he, isWire, Bool.false_eq_true] at hw
      | wire a b => simp only [Pages.lowerLevel, he, Page.depth, hanc, Finset.card_empty, Nat.sub_zero]
    have hsup := Finset.le_sup (s := Finset.univ) (f := p.lowerLevel) (Finset.mem_univ i)
    have hh := le_max_right (Finset.univ.sup p.upperLevel) (Finset.univ.sup p.lowerLevel)
    unfold Pages.highest
    omega
  · have htriple (i : p.lowerPage.Index) : ∃ a, p.lowerPage.group i = .triple a := by
      cases he : p.lowerPage.group i with
      | triple a => exact ⟨a, rfl⟩
      | wire a b =>
        exact (hn ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by rw [he]; rfl⟩⟩).elim
    have hmax : p.lowerPage.maxActive ≤ 1 := by
      apply Finset.sup_le
      intro gap _
      apply Finset.card_le_one.mpr
      intro i hi j hj
      by_contra hij
      have hia := (Finset.mem_filter.mp hi).2
      have hja := (Finset.mem_filter.mp hj).2
      obtain ⟨a, ha⟩ := htriple i
      obtain ⟨b, hb⟩ := htriple j
      rcases hp.lower.noncrossing i j hij with h | h | h | h
      · omega
      · omega
      · exact Page.triple_leaf hp.lower ha h
      · exact Page.triple_leaf hp.lower hb h
    by_cases hi : Nonempty p.lowerPage.Index
    · obtain ⟨i⟩ := hi
      obtain ⟨a, ha⟩ := htriple i
      have hsup := Finset.le_sup (s := Finset.univ) (f := p.lowerLevel) (Finset.mem_univ i)
      have hl : p.lowerLevel i = 1 := by simp only [Pages.lowerLevel, ha]
      have hh := le_max_right (Finset.univ.sup p.upperLevel) (Finset.univ.sup p.lowerLevel)
      unfold Pages.highest
      omega
    · have : IsEmpty p.lowerPage.Index := not_nonempty_iff.mp hi
      have hempty (gap : ℕ) : p.lowerPage.active gap = ∅ := by ext i; exact isEmptyElim i
      apply Finset.sup_le
      intro gap _
      rw [hempty, Finset.card_empty]
      exact Nat.zero_le _

/-- Constant source upper and lower active budgets give a constant repaired scale budget. -/
private theorem repair_highest_le {l : PortLayout} (hl : l.pages.Valid) {upper lower : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ upper) (hb : l.pages.lowerPage.maxActive ≤ lower) :
    (Cuts.repair l).layout.pages.highest ≤ 2 * max upper lower + 2 := by
  apply Pages.highest_le_repaired _ upper lower (repair_upper_maxActive hl hu)
  have h := repair_lower_maxActive hl hu hb
  omega

/-- The original highest working level controls the repaired lower budget. -/
theorem repair_highest_le_source {l : PortLayout} (hl : l.pages.Valid) {upper : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ upper) :
    (Cuts.repair l).layout.pages.highest ≤ 2 * max upper l.pages.highest + 2 :=
  repair_highest_le hl hu (lower_maxActive_le_highest hl)

/-- Fixed upper source depth gives linear port growth under the literal complete repair. -/
theorem repair_portCount_le {l : PortLayout} (hl : l.pages.Valid) {upper : ℕ}
    (hu : l.pages.upperPage.maxActive ≤ upper) :
    (Cuts.repair l).layout.portCount ≤ 3 * l.portCount + 6 * l.portCount * (upper + 1) := by
  have h := cut_scan_counts (bufferInternal l) (List.range (bufferInternal l).layout.portCount).reverse
    (internal_upperLoad_le hl hu)
  simp only [List.length_reverse, List.length_range] at h
  have hn := bufferInternal_count l
  change (Cuts.repair l).layout.portCount ≤ _ ∧ _ at h
  nlinarith [h.1]

end PushPuzzle.Push.Partner.Resources

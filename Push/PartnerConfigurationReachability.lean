/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationStep
import all Push.PartnerConfiguration
import all Push.PartnerConfigurationStep
import all Push.PartnerValidity

/-! Original legal axis reversals lift through the actual three-axis ear chain. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

/-- Every original axis reversal has a concrete legal macro on the emitted ear layout. -/
private theorem earExtend_step {l : PortLayout} (hl : PortInventory l) {cut : ℕ}
    (hc : cut ≤ l.portCount)
    (hsafe : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes next : List Bool}
    (hstep : l.AxisStep axes next) :
    Relation.ReflTransGen (ear l cut ab).AxisStep (earExtend l cut ab axes) (earExtend l cut ab next) := by
  obtain ⟨hs, index, hi, rfl, ht⟩ := hstep
  have hstart := earExtend_legal hl hc hsafe hp hs
  have hgoal := earExtend_legal hl hc hsafe hp ht
  by_cases hindex : index = ab.2
  · subst index
    let next := axes.set ab.2 (!(axes.getD ab.2 false))
    have hbound := upper_bounds hl hp
    have hnew : next.getD ab.2 false = !(axes.getD ab.2 false) :=
      List.getD_set_self (by simpa only [hs.axes_length] using hbound.2)
    have hab := upper_endpoints_ne hl hp
    have ha : next.getD ab.1 false = axes.getD ab.1 false := List.getD_set_ne (Ne.symm hab)
    change Relation.ReflTransGen (ear l cut ab).AxisStep
      (earState l cut axes (!(axes.getD ab.2 false)) (axes.getD ab.2 false))
      (earState l cut next (!(next.getD ab.2 false)) (next.getD ab.2 false))
    change (ear l cut ab).InputLegal (earState l cut next (!(next.getD ab.2 false)) (next.getD ab.2 false)) at hgoal
    cases hbit : axes.getD ab.2 false with
    | false =>
      have haTrue : axes.getD ab.1 false = true := by
        have h := hs.upper _ _ hp
        simpa only [hbit, Bool.false_eq_true, or_false] using h
      have hbTrue : next.getD ab.2 false = true := by rw [hnew, hbit]; rfl
      have hnTrue : next.getD ab.1 false = true := ha.trans haTrue
      have hm₁ := earState_legal hl hc hsafe hp ht true false (Or.inl hnTrue) (Or.inl hbTrue) (Or.inr rfl)
      have hm₂ := earState_legal hl hc hsafe hp ht false false (Or.inl hnTrue) (Or.inl hbTrue) (Or.inl rfl)
      have hstart' : (ear l cut ab).InputLegal (earState l cut axes true false) := by
        simpa only [earExtend, hbit, Bool.not_false] using hstart
      have hgoal' : (ear l cut ab).InputLegal (earState l cut next false true) := by
        rw [hbTrue] at hgoal
        exact hgoal
      have h₁ := earState_old_reachable hi (next := next) rfl hstart' hm₁
      have h₂ := earState_p_reachable hc hm₁ hm₂
      have h₃ := earState_q_reachable hc hm₂ hgoal'
      rw [hbTrue]
      exact h₁.trans (h₂.trans h₃)
    | true =>
      have hbFalse : next.getD ab.2 false = false := by rw [hnew, hbit]; rfl
      have hnTrue : next.getD ab.1 false = true := by
        have h := ht.upper _ _ hp
        change next.getD ab.1 false = true ∨ next.getD ab.2 false = true at h
        simpa only [hbFalse, Bool.false_eq_true, or_false] using h
      have haTrue : axes.getD ab.1 false = true := ha.symm.trans hnTrue
      have hm₁ := earState_legal hl hc hsafe hp hs false false (Or.inl haTrue) (Or.inl hbit) (Or.inl rfl)
      have hm₂ := earState_legal hl hc hsafe hp hs true false (Or.inl haTrue) (Or.inl hbit) (Or.inr rfl)
      have hstart' : (ear l cut ab).InputLegal (earState l cut axes false true) := by
        simpa only [earExtend, hbit, Bool.not_true] using hstart
      have hgoal' : (ear l cut ab).InputLegal (earState l cut next true false) := by
        rw [hbFalse] at hgoal
        exact hgoal
      have h₁ := earState_q_reachable hc hstart' hm₁
      have h₂ := earState_p_reachable hc hm₁ hm₂
      have h₃ := earState_old_reachable hi (next := next) rfl hm₂ hgoal'
      rw [hbFalse]
      exact h₁.trans (h₂.trans h₃)
  · have hb : (axes.set index (!(axes.getD index false))).getD ab.2 false = axes.getD ab.2 false :=
      List.getD_set_ne hindex
    have hgoal' : (ear l cut ab).InputLegal
        (earState l cut (axes.set index (!(axes.getD index false))) (!(axes.getD ab.2 false)) (axes.getD ab.2 false)) := by
      simpa only [earExtend, hb] using hgoal
    change Relation.ReflTransGen (ear l cut ab).AxisStep
      (earState l cut axes (!(axes.getD ab.2 false)) (axes.getD ab.2 false))
      (earState l cut (axes.set index (!(axes.getD index false)))
        (!((axes.set index (!(axes.getD index false))).getD ab.2 false))
        ((axes.set index (!(axes.getD index false))).getD ab.2 false))
    rw [hb]
    exact earState_old_reachable hi rfl hstart hgoal'

/-- The actual standard direction extension preserves and reflects complete legal axis reachability. -/
theorem earExtend_reachable_iff {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hsafe : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) (axes next : List Bool)
    (hlen : axes.length = l.portCount) (hnlen : next.length = l.portCount) :
    Relation.ReflTransGen (ear l cut ab).AxisStep (earExtend l cut ab axes) (earExtend l cut ab next) ↔
      Relation.ReflTransGen l.AxisStep axes next := by
  constructor
  · intro hr
    have hproject : ∀ {s t}, Relation.ReflTransGen (ear l cut ab).AxisStep s t →
        Relation.ReflTransGen l.AxisStep (earRestrict l cut s) (earRestrict l cut t) := by
      intro s t h
      induction h with
      | refl => exact .refl
      | tail _ hm ih =>
        rcases earRestrict_step hl hc hsafe hp hm with he | hstep
        · exact he ▸ ih
        · exact ih.tail hstep
    have h := hproject hr
    rwa [earRestrict_extend l cut ab axes hlen, earRestrict_extend l cut ab next hnlen] at h
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact (ih hm.1.axes_length).trans (earExtend_step hl hc hsafe hp hm)

end PushPuzzle.Push.Partner

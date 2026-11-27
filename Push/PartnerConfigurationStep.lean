/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfiguration
public import CslibFrontier.Foundations.Data.List.Lookup
import all Push.PartnerConfiguration

/-! Single-axis readout and concrete one-axis updates of the actual ear direction words. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

private theorem words_eq_of_reads {a b : List Bool} (hlen : a.length = b.length)
    (hread : ∀ i < a.length, a.getD i false = b.getD i false) : a = b := by
  apply List.ext_getElem hlen
  intro i hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using hread i hi

private theorem eq_or_axisStep_of_agree_off {l : PortLayout} {axes next : List Bool}
    (hs : l.InputLegal axes) (ht : l.InputLegal next) {index : ℕ} (hi : index < l.portCount)
    (hread : ∀ site < l.portCount, site ≠ index → axes.getD site false = next.getD site false) :
    axes = next ∨ l.AxisStep axes next := by
  by_cases he : axes.getD index false = next.getD index false
  · apply Or.inl
    apply words_eq_of_reads (hs.axes_length.trans ht.axes_length.symm)
    intro i hib
    have hip : i < l.portCount := by simpa only [hs.axes_length] using hib
    by_cases h : i = index
    · exact h ▸ he
    · exact hread i hip h
  · apply Or.inr
    refine ⟨hs, index, hi, ?_, ht⟩
    apply words_eq_of_reads (by simp only [List.length_set, hs.axes_length, ht.axes_length])
    intro site hsite
    have hbound : site < l.portCount := by simpa only [ht.axes_length] using hsite
    by_cases h : site = index
    · subst site
      rw [List.getD_set_self (by simpa only [hs.axes_length] using hi)]
      exact Bool.eq_not_iff.mpr (Ne.symm he)
    · rw [List.getD_set_ne (Ne.symm h)]
      exact (hread site hbound h).symm

private theorem reachable_of_agree_off {l : PortLayout} {axes next : List Bool}
    (hs : l.InputLegal axes) (ht : l.InputLegal next) {index : ℕ} (hi : index < l.portCount)
    (hread : ∀ site < l.portCount, site ≠ index → axes.getD site false = next.getD site false) :
    Relation.ReflTransGen l.AxisStep axes next := by
  rcases eq_or_axisStep_of_agree_off hs ht hi hread with rfl | h
  · exact .refl
  · exact .single h

private theorem shift_unshift (cut i : ℕ) (hp : i ≠ cut) (hq : i ≠ cut + 1) : shift cut (unshift cut i) = i := by
  unfold shift unshift
  split_ifs <;> omega

private theorem earState_p_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {ab : ℕ × ℕ} {axes : List Bool} {p p' q : Bool}
    (hs : (ear l cut ab).InputLegal (earState l cut axes p q))
    (ht : (ear l cut ab).InputLegal (earState l cut axes p' q)) :
    Relation.ReflTransGen (ear l cut ab).AxisStep (earState l cut axes p q) (earState l cut axes p' q) := by
  apply reachable_of_agree_off hs ht (index := cut) (by change cut < l.portCount + 2; omega)
  intro site hsite hne
  rw [earState_get l cut axes p q hsite, earState_get l cut axes p' q hsite]
  simp only [earValue, ite_eq_right hne]

private theorem earState_q_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {ab : ℕ × ℕ} {axes : List Bool} {p q q' : Bool}
    (hs : (ear l cut ab).InputLegal (earState l cut axes p q))
    (ht : (ear l cut ab).InputLegal (earState l cut axes p q')) :
    Relation.ReflTransGen (ear l cut ab).AxisStep (earState l cut axes p q) (earState l cut axes p q') := by
  apply reachable_of_agree_off hs ht (index := cut + 1) (by change cut + 1 < l.portCount + 2; omega)
  intro site hsite hne
  rw [earState_get l cut axes p q hsite, earState_get l cut axes p q' hsite]
  simp only [earValue, ite_eq_right hne]

private theorem earState_old_reachable {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ}
    {axes next : List Bool} {p q : Bool} {index : ℕ} (hi : index < l.portCount)
    (he : next = axes.set index (!(axes.getD index false)))
    (hs : (ear l cut ab).InputLegal (earState l cut axes p q))
    (ht : (ear l cut ab).InputLegal (earState l cut next p q)) :
    Relation.ReflTransGen (ear l cut ab).AxisStep (earState l cut axes p q) (earState l cut next p q) := by
  apply reachable_of_agree_off hs ht (index := shift cut index) (shift_lt cut hi)
  intro site hsite hne
  rw [earState_get l cut axes p q hsite, earState_get l cut next p q hsite]
  unfold earValue
  split_ifs with hp hq
  all_goals try rfl
  have hindex : index ≠ unshift cut site := by
    intro heq
    have hback := shift_unshift cut site hp hq
    rw [← heq] at hback
    exact hne hback.symm
  rw [he, List.getD_set_ne hindex]

/-- Every real new-axis flip projects to stuttering or one legal old-axis flip. -/
theorem earRestrict_step {l : PortLayout} (hl : PortInventory l) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {ab : ℕ × ℕ} (hp : ab ∈ l.upperPairs) {axes next : List Bool}
    (hstep : (ear l cut ab).AxisStep axes next) :
    earRestrict l cut axes = earRestrict l cut next ∨
      l.AxisStep (earRestrict l cut axes) (earRestrict l cut next) := by
  obtain ⟨haxes, i, hi, rfl, hnext⟩ := hstep
  have hsource := earRestrict_legal hl hs hp haxes
  have htarget := earRestrict_legal hl hs hp hnext
  by_cases hfresh : i = cut ∨ i = cut + 1
  · apply Or.inl
    apply words_eq_of_reads (hsource.axes_length.trans htarget.axes_length.symm)
    intro site hsite
    have hb : site < l.portCount := by simpa only [hsource.axes_length] using hsite
    rw [earRestrict_get l cut axes hb, earRestrict_get l cut _ hb]
    apply Eq.symm
    apply List.getD_set_ne
    rcases hfresh with hfresh | hfresh
    · exact fun he => shift_ne_cut cut site (he.symm.trans hfresh)
    · exact fun he => shift_ne_cut_succ cut site (he.symm.trans hfresh)
  · have hpi : i ≠ cut := fun h => hfresh (Or.inl h)
    have hqi : i ≠ cut + 1 := fun h => hfresh (Or.inr h)
    have hback := shift_unshift cut i hpi hqi
    have hindex : unshift cut i < l.portCount := by
      change i < l.portCount + 2 at hi
      unfold unshift
      split_ifs <;> omega
    apply eq_or_axisStep_of_agree_off hsource htarget hindex
    intro site hsite hne
    rw [earRestrict_get l cut axes hsite, earRestrict_get l cut _ hsite]
    apply Eq.symm
    apply List.getD_set_ne
    intro he
    have he' := (shift_injective cut) (hback.trans he)
    exact hne he'.symm

end PushPuzzle.Push.Partner

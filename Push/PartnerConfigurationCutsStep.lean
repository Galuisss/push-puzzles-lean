/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationCutsLegal
import all Push.PartnerConfigurationCuts
import all Push.PartnerConfigurationStep

/-! Actual old-axis and fresh-axis moves of a simultaneous cut. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

private def oldIndex (cut count i : ℕ) : ℕ := if i < cut then i else i - 2 * count

private theorem shift_oldIndex (cut count i : ℕ) (hfresh : ¬(cut ≤ i ∧ i < cut + 2 * count)) :
    shift cut count (oldIndex cut count i) = i := by
  unfold oldIndex shift
  split_ifs <;> omega

private theorem cutState_left_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {axes leftValues rightValues : List Bool} {j : ℕ} (hj : j < (active l cut).length) (value : Bool)
    (hs : (compile l cut).InputLegal (cutState l cut axes leftValues rightValues))
    (ht : (compile l cut).InputLegal (cutState l cut axes (leftValues.set j value) rightValues)) :
    Relation.ReflTransGen (compile l cut).AxisStep (cutState l cut axes leftValues rightValues)
      (cutState l cut axes (leftValues.set j value) rightValues) := by
  have hb := left_bounds (cut := cut) hj
  apply reachable_of_agree_off hs ht (index := left cut (active l cut).length j)
    (by change _ < l.portCount + 2 * _; omega)
  intro site hsite hne
  rw [cutState_get l cut axes leftValues rightValues hsite,
    cutState_get l cut axes (leftValues.set j value) rightValues hsite]
  unfold cutValue
  dsimp only
  split_ifs with h₁ h₂ h₃ <;> try rfl
  have hidx : j ≠ cut + (active l cut).length - 1 - site := by
    unfold left at hne
    omega
  rw [List.getD_set_ne hidx]

private theorem cutState_right_reachable {l : PortLayout} {cut : ℕ} (hc : cut ≤ l.portCount)
    {axes leftValues rightValues : List Bool} {j : ℕ} (hj : j < (active l cut).length) (value : Bool)
    (hs : (compile l cut).InputLegal (cutState l cut axes leftValues rightValues))
    (ht : (compile l cut).InputLegal (cutState l cut axes leftValues (rightValues.set j value))) :
    Relation.ReflTransGen (compile l cut).AxisStep (cutState l cut axes leftValues rightValues)
      (cutState l cut axes leftValues (rightValues.set j value)) := by
  have hb := right_bounds (cut := cut) hj
  apply reachable_of_agree_off hs ht (index := right cut (active l cut).length j)
    (by change _ < l.portCount + 2 * _; omega)
  intro site hsite hne
  rw [cutState_get l cut axes leftValues rightValues hsite,
    cutState_get l cut axes leftValues (rightValues.set j value) hsite]
  unfold cutValue
  dsimp only
  split_ifs with h₁ h₂ h₃ <;> try rfl
  have hidx : j ≠ site - cut - (active l cut).length := by
    unfold right at hne
    omega
  rw [List.getD_set_ne hidx]

private theorem cutState_old_reachable {l : PortLayout} {cut : ℕ} {axes next leftValues rightValues : List Bool}
    {index : ℕ} (hi : index < l.portCount) (he : next = axes.set index (!(axes.getD index false)))
    (hs : (compile l cut).InputLegal (cutState l cut axes leftValues rightValues))
    (ht : (compile l cut).InputLegal (cutState l cut next leftValues rightValues)) :
    Relation.ReflTransGen (compile l cut).AxisStep (cutState l cut axes leftValues rightValues)
      (cutState l cut next leftValues rightValues) := by
  apply reachable_of_agree_off hs ht (index := shift cut (active l cut).length index) (shift_lt cut _ hi)
  intro site hsite hne
  rw [cutState_get l cut axes leftValues rightValues hsite, cutState_get l cut next leftValues rightValues hsite]
  unfold cutValue
  dsimp only
  split_ifs with h₁ h₂ h₃
  · have hidx : index ≠ site := by
      intro h
      subst index
      exact hne (by simp only [shift, ite_eq_left h₁])
    rw [he, List.getD_set_ne hidx]
  · rfl
  · rfl
  · have hidx : index ≠ site - 2 * (active l cut).length := by
      intro h
      unfold shift at hne
      split_ifs at hne <;> omega
    rw [he, List.getD_set_ne hidx]

/-- Any legal actual new-axis reversal reads back as stuttering or one original legal reversal. -/
theorem cutRestrict_step {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hs : SafeCut l cut) {axes next : List Bool} (hstep : (compile l cut).AxisStep axes next) :
    cutRestrict l cut axes = cutRestrict l cut next ∨ l.AxisStep (cutRestrict l cut axes) (cutRestrict l cut next) := by
  obtain ⟨haxes, i, hi, rfl, hnext⟩ := hstep
  have hsource := cutRestrict_legal hl hs haxes
  have htarget := cutRestrict_legal hl hs hnext
  by_cases hfresh : cut ≤ i ∧ i < cut + 2 * (active l cut).length
  · apply Or.inl
    apply words_eq_of_reads (hsource.axes_length.trans htarget.axes_length.symm)
    intro site hsite
    have hb : site < l.portCount := by simpa only [hsource.axes_length] using hsite
    rw [cutRestrict_get l cut axes hb, cutRestrict_get l cut _ hb]
    exact (List.getD_set_ne (Ne.symm (shift_ne_fresh cut _ site hfresh))).symm
  · have hback := shift_oldIndex cut (active l cut).length i hfresh
    have hindex : oldIndex cut (active l cut).length i < l.portCount := by
      change i < l.portCount + 2 * (active l cut).length at hi
      unfold oldIndex
      split_ifs <;> omega
    apply eq_or_axisStep_of_agree_off hsource htarget hindex
    intro site hsite hne
    rw [cutRestrict_get l cut axes hsite, cutRestrict_get l cut _ hsite]
    apply Eq.symm
    apply List.getD_set_ne
    intro he
    exact hne ((shift_injective cut _) (hback.trans he)).symm

end PushPuzzle.Push.Partner.Cuts

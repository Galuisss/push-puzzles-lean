/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerConfigurationCutsCursor
import all Push.PartnerConfiguration
import all Push.PartnerConfigurationCutsCursor
import all Push.PartnerConfigurationCutsStep
import all Push.PartnerCutsPaths

/-! Full weighted axis reachability through the actual simultaneous upper-WIRE subdivision. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Cuts

open PushS

/-- Every old axis reversal lifts to a concrete one- or three-axis macro in the actual common-cut board. -/
private theorem cutExtend_step {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ}
    (hc : cut ≤ l.portCount)
    (hsafe : SafeCut l cut) {axes next : List Bool} (hstep : l.AxisStep axes next) :
    Relation.ReflTransGen (compile l cut).AxisStep (cutExtend l cut axes) (cutExtend l cut next) := by
  obtain ⟨hs, index, hi, rfl, ht⟩ := hstep
  have hstart := cutExtend_legal hl hc hsafe hs
  have hgoal := cutExtend_legal hl hc hsafe ht
  by_cases hex : ∃ owner ∈ (active l cut).zipIdx, owner.1.2 = index
  · obtain ⟨owner, hp, hindex⟩ := hex
    subst index
    let next := axes.set owner.1.2 (!(axes.getD owner.1.2 false))
    have hmem := ((mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)).1
    have hab := upper_endpoints_ne (inventory_of_pages hl) hmem
    have hbound := upper_bounds (inventory_of_pages hl) hmem
    have hnew : next.getD owner.1.2 false = !(axes.getD owner.1.2 false) :=
      List.getD_set_self (by simpa only [hs.axes_length] using hbound.2)
    have ha : next.getD owner.1.1 false = axes.getD owner.1.1 false := List.getD_set_ne (Ne.symm hab)
    change Relation.ReflTransGen (compile l cut).AxisStep (cutExtend l cut axes) (cutExtend l cut next)
    rw [← overrideState_eq_extend hp axes, ← overrideState_eq_extend hp next]
    have hstart' : (compile l cut).InputLegal
        (overrideState l cut axes owner.2 (axes.getD owner.1.2 false) (!(axes.getD owner.1.2 false))) := by
      rw [overrideState_eq_extend hp axes]
      exact hstart
    have hgoal' : (compile l cut).InputLegal
        (overrideState l cut next owner.2 (next.getD owner.1.2 false) (!(next.getD owner.1.2 false))) := by
      rw [overrideState_eq_extend hp next]
      exact hgoal
    cases hbit : axes.getD owner.1.2 false with
    | false =>
      have haTrue : axes.getD owner.1.1 false = true := by
        have h := hs.upper _ _ hmem
        simpa only [hbit, Bool.false_eq_true, or_false] using h
      have hbTrue : next.getD owner.1.2 false = true := by rw [hnew, hbit]; rfl
      have hnTrue := ha.trans haTrue
      have hsource : (compile l cut).InputLegal (overrideState l cut axes owner.2 false true) := by
        simpa only [hbit, Bool.not_false] using hstart'
      have htarget : (compile l cut).InputLegal (overrideState l cut next owner.2 true false) := by
        rw [hbTrue] at hgoal'
        exact hgoal'
      have hm₁ := overrideState_legal hl hc hsafe hp ht false true (Or.inl hnTrue) (Or.inr rfl) (Or.inl rfl)
      have hm₂ := overrideState_legal hl hc hsafe hp ht false false (Or.inl hnTrue) (Or.inl hbTrue) (Or.inl rfl)
      have h₁ := overrideState_old_reachable hl hp (next := next) rfl hsource hm₁
      have h₂ := overrideState_right_reachable hc hp hm₁ hm₂
      have h₃ := overrideState_left_reachable hc hp hm₂ htarget
      rw [hbTrue]
      exact h₁.trans (h₂.trans h₃)
    | true =>
      have hbFalse : next.getD owner.1.2 false = false := by rw [hnew, hbit]; rfl
      have hnTrue : next.getD owner.1.1 false = true := by
        have h := ht.upper _ _ hmem
        change next.getD owner.1.1 false = true ∨ next.getD owner.1.2 false = true at h
        simpa only [hbFalse, Bool.false_eq_true, or_false] using h
      have haTrue := ha.symm.trans hnTrue
      have hsource : (compile l cut).InputLegal (overrideState l cut axes owner.2 true false) := by
        simpa only [hbit, Bool.not_true] using hstart'
      have htarget : (compile l cut).InputLegal (overrideState l cut next owner.2 false true) := by
        rw [hbFalse] at hgoal'
        exact hgoal'
      have hm₁ := overrideState_legal hl hc hsafe hp hs false false (Or.inl haTrue) (Or.inl hbit) (Or.inl rfl)
      have hm₂ := overrideState_legal hl hc hsafe hp hs false true (Or.inl haTrue) (Or.inr rfl) (Or.inl rfl)
      have h₁ := overrideState_left_reachable hc hp hsource hm₁
      have h₂ := overrideState_right_reachable hc hp hm₁ hm₂
      have h₃ := overrideState_old_reachable hl hp (next := next) rfl hm₂ htarget
      rw [hbFalse]
      exact h₁.trans (h₂.trans h₃)
  · have hvalues (negate : Bool) : activeValues l cut axes negate =
        activeValues l cut (axes.set index (!(axes.getD index false))) negate := by
      apply activeValues_congr
      intro ab hab
      apply Eq.symm
      apply List.getD_set_ne
      intro he
      obtain ⟨j, hj⟩ := active_zip_exists hab
      exact hex ⟨(ab, j), hj, he.symm⟩
    change Relation.ReflTransGen (compile l cut).AxisStep
      (cutState l cut axes (activeValues l cut axes false) (activeValues l cut axes true))
      (cutState l cut (axes.set index (!(axes.getD index false)))
        (activeValues l cut (axes.set index (!(axes.getD index false))) false)
        (activeValues l cut (axes.set index (!(axes.getD index false))) true))
    have hgoal' : (compile l cut).InputLegal (cutState l cut (axes.set index (!(axes.getD index false)))
        (activeValues l cut axes false) (activeValues l cut axes true)) := by
      simpa only [cutExtend, ← hvalues false, ← hvalues true] using hgoal
    rw [← hvalues false, ← hvalues true]
    exact cutState_old_reachable hi rfl hstart hgoal'

/-- The actual simultaneous-cut direction emitter preserves and reflects original weighted axis reachability. -/
theorem cutExtend_reachable_iff {l : PortLayout} (hl : l.pages.Valid) {cut : ℕ} (hc : cut ≤ l.portCount)
    (hsafe : SafeCut l cut) (axes next : List Bool) (hlen : axes.length = l.portCount) (hnlen : next.length = l.portCount) :
    Relation.ReflTransGen (compile l cut).AxisStep (cutExtend l cut axes) (cutExtend l cut next) ↔
      Relation.ReflTransGen l.AxisStep axes next := by
  constructor
  · intro hr
    have hproject : ∀ {s t}, Relation.ReflTransGen (compile l cut).AxisStep s t →
        Relation.ReflTransGen l.AxisStep (cutRestrict l cut s) (cutRestrict l cut t) := by
      intro s t h
      induction h with
      | refl => exact .refl
      | tail _ hm ih =>
        rcases cutRestrict_step hl hc hsafe hm with he | hstep
        · exact he ▸ ih
        · exact ih.tail hstep
    have h := hproject hr
    rwa [cutRestrict_extend l cut axes hlen, cutRestrict_extend l cut next hnlen] at h
  · intro hr
    induction hr with
    | refl => exact .refl
    | tail _ hm ih => exact (ih hm.1.axes_length).trans (cutExtend_step hl hc hsafe hm)

end PushPuzzle.Push.Partner.Cuts

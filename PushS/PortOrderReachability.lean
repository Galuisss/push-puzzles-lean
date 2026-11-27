/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrderUpdates
import all PushS.PortOrderProjection
import all PushS.PortOrderUpdates
import all PushS.PortInputStep

/-! Legal actual axis paths lift to ordered paths between the same ordered endpoints. -/

public section
namespace PushPuzzle.PushS.PortLayout


private theorem any_congr_mem {α : Type} (tokens : List α) (left right : α → Bool)
    (he : ∀ token ∈ tokens, left token = right token) : tokens.any left = tokens.any right := by
  induction tokens with
  | nil => rfl
  | cons token tail ih =>
    simp only [List.any_cons, he token List.mem_cons_self]
    rw [ih (fun t ht => he t (List.mem_cons_of_mem _ ht))]

private theorem promotion_set (l : PortLayout) (axes : List Bool) (index : ℕ) (bit : Bool)
    (hi : index < axes.length) (site : ℕ)
    (hn : site ≠ index + 1 ∨ .gate .andGate index ∉ l.lowerGroups) :
    promotion l (axes.set index bit) site = promotion l axes site := by
  unfold promotion
  apply any_congr_mem
  intro group hg
  cases group with
  | wire a b => rfl
  | gate kind first =>
    cases kind with
    | orGate => rfl
    | andGate =>
      change (decide (site = first + 1) && (axes.set index bit).getD first false) = _
      by_cases hf : first = index
      · subst first
        rcases hn with hn | hn
        · simp only [hn, decide_false, Bool.false_and]
        · exact False.elim (hn hg)
      · rw [read_set axes index bit hi first, ite_eq_right hf]

private theorem orderAxes_set_read (l : PortLayout) (axes : List Bool) (index : ℕ) (bit : Bool)
    (hi : index < axes.length) (site : ℕ) (hne : site ≠ index)
    (hn : site ≠ index + 1 ∨ .gate .andGate index ∉ l.lowerGroups) :
    (l.orderAxes (axes.set index bit)).getD site false = (l.orderAxes axes).getD site false := by
  by_cases hs : site < l.portCount
  · rw [orderAxes_read l _ hs, orderAxes_read l axes hs, read_set axes index bit hi site,
      ite_eq_right hne, promotion_set l axes index bit hi site hn]
  · rw [List.getD_eq_default _ _ (by simpa only [length_orderAxes] using Nat.le_of_not_gt hs),
      List.getD_eq_default _ _ (by simpa only [length_orderAxes] using Nat.le_of_not_gt hs)]

private theorem ordered_path_symm {l : PortLayout} {axes next : List Bool}
    (h : Relation.ReflTransGen l.OrderedAxisStep axes next) :
    Relation.ReflTransGen l.OrderedAxisStep next axes := by
  induction h with
  | refl => exact .refl
  | tail path step ih => exact (Relation.ReflTransGen.single step.symm).trans ih

private theorem order_flip_left (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes next : List Bool)
    (ha : l.InputLegal axes) (hn : l.InputLegal next) (index : ℕ) (hi : index < l.portCount)
    (he : next = axes.set index (!(axes.getD index false))) (hf : axes.getD index false = false)
    (hg : .gate .andGate index ∈ l.lowerGroups) :
    Relation.ReflTransGen l.OrderedAxisStep (l.orderAxes axes) (l.orderAxes next) := by
  have hindex : index < axes.length := by rw [ha.axes_length]; exact hi
  have hleft : next.getD index false = true := by
    rw [he, read_set axes index _ hindex index, ite_eq_left rfl, hf]
    rfl
  have hheavy : axes.getD (index + 2) false = false := by
    rcases hn.and_gate index hg with hh | ⟨hh, _⟩
    · rwa [he, read_set axes index _ hindex (index + 2), ite_eq_right (by omega)] at hh
    · rw [hleft] at hh
      cases hh
  have hp := orderAxes_ordered l hl axes ha
  have hq := orderAxes_ordered l hl next hn
  have hh : (l.orderAxes axes).getD (index + 2) false = false :=
    (orderAxes_gate l hl axes hg).2.2.trans hheavy
  have hmid : index + 1 < l.portCount :=
    lower_port_lt l hl hg (by simp [LowerGroup.shape, PageLevels.Group.ports])
  have hm := hp.set_middle_true hl hg hh
  have hfirst := hp.reachable_of_agree_off hm (index + 1) hmid (fun site hs => by
    rw [read_set _ _ true (by rw [hp.axes_length]; exact hmid) site, ite_eq_right hs])
  have hlast := hm.reachable_of_agree_off hq index hi (fun site hs => by
    by_cases heq : site = index + 1
    · subst site
      rw [read_set _ _ true (by rw [hp.axes_length]; exact hmid) _, ite_eq_left rfl,
        (orderAxes_gate l hl next hg).2.1, ite_eq_left rfl, hleft, Bool.or_true]
    · rw [read_set _ _ true (by rw [hp.axes_length]; exact hmid) site, ite_eq_right heq]
      rw [he, orderAxes_set_read l axes index _ hindex site hs (Or.inl heq)])
  exact hfirst.trans hlast

private theorem order_flip_false (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes next : List Bool)
    (ha : l.InputLegal axes) (hn : l.InputLegal next) (index : ℕ) (hi : index < l.portCount)
    (he : next = axes.set index (!(axes.getD index false))) (hf : axes.getD index false = false) :
    Relation.ReflTransGen l.OrderedAxisStep (l.orderAxes axes) (l.orderAxes next) := by
  by_cases hg : .gate .andGate index ∈ l.lowerGroups
  · exact order_flip_left l hl axes next ha hn index hi he hf hg
  · apply (orderAxes_ordered l hl axes ha).reachable_of_agree_off (orderAxes_ordered l hl next hn) index hi
    intro site hs
    rw [he, orderAxes_set_read l axes index _ (by rw [ha.axes_length]; exact hi) site hs (Or.inr hg)]

/-- Every actual legal single-axis flip lifts to an ordered path between its same projected arrays.
-/
theorem orderAxes_step {l : PortLayout} (hl : l.pages.lowerPage.Valid) {axes next : List Bool}
    (h : l.AxisStep axes next) :
    Relation.ReflTransGen l.OrderedAxisStep (l.orderAxes axes) (l.orderAxes next) := by
  obtain ⟨ha, index, hi, rfl, hn⟩ := h
  cases hf : axes.getD index false with
  | false =>
    simpa only [hf] using order_flip_false l hl axes
      (axes.set index (!(axes.getD index false))) ha hn index hi rfl hf
  | true =>
    have hindex : index < axes.length := by rw [ha.axes_length]; exact hi
    have hfalse : (axes.set index (!(axes.getD index false))).getD index false = false := by
      rw [getD_flip axes index hindex, hf]
      rfl
    have hp := order_flip_false l hl (axes.set index (!(axes.getD index false))) axes hn ha index hi
      (flip_twice axes index hindex).symm hfalse
    simpa only [hf] using ordered_path_symm hp

/-- Between ordered actual inputs, legal axis reachability is exactly ordered axis reachability.
-/
theorem axisReachable_iff_orderedReachable (l : PortLayout) (hl : l.pages.lowerPage.Valid)
    (axes next : List Bool) (ha : l.OrderedInputs axes) (hn : l.OrderedInputs next) :
    Relation.ReflTransGen l.AxisStep axes next ↔ Relation.ReflTransGen l.OrderedAxisStep axes next := by
  constructor
  · intro hr
    have hp := Relation.ReflTransGen.lift' l.orderAxes (fun _ _ h => orderAxes_step hl h) _ _ hr
    change Relation.ReflTransGen l.OrderedAxisStep (l.orderAxes axes) (l.orderAxes next) at hp
    rwa [orderAxes_eq_of_ordered l axes ha, orderAxes_eq_of_ordered l next hn] at hp
  · intro hr
    exact Relation.ReflTransGen.lift id (fun _ _ h => h.toAxisStep) _ _ hr

end PushPuzzle.PushS.PortLayout

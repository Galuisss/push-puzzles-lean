/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrderProjection
import all PushS.PortOrderProjection

/-! Actual single-axis updates and the safe middle promotion at an ordered AND core. -/

public section
namespace PushPuzzle.PushS.PortLayout


private theorem read_set (axes : List Bool) (index : ℕ) (bit : Bool) (hi : index < axes.length) (site : ℕ) :
    (axes.set index bit).getD site false = if site = index then bit else axes.getD site false := by
  by_cases he : site = index
  · subst site
    rw [ite_eq_left rfl, List.getD_eq_getElem _ _ (by simpa only [List.length_set] using hi)]
    exact List.getElem_set_self _
  · rw [ite_eq_right he]
    by_cases ha : site < axes.length
    · rw [List.getD_eq_getElem _ _ (by simpa only [List.length_set] using ha),
        List.getD_eq_getElem _ _ ha]
      exact List.getElem_set_ne (Ne.symm he) _
    · rw [List.getD_eq_default _ _ (by simpa only [List.length_set] using Nat.le_of_not_gt ha),
        List.getD_eq_default _ _ (Nat.le_of_not_gt ha)]

private theorem axes_eq_of_reads (left right : List Bool) (hlen : left.length = right.length)
    (he : ∀ index, left.getD index false = right.getD index false) : left = right := by
  apply List.ext_getElem hlen
  intro index hi hj
  simpa only [List.getD_eq_getElem _ _ hi, List.getD_eq_getElem _ _ hj] using he index

/-- Two ordered arrays agreeing away from one original axis are connected by site most one flip.
-/
theorem OrderedInputs.reachable_of_agree_off {l : PortLayout} {axes next : List Bool}
    (ha : l.OrderedInputs axes) (hn : l.OrderedInputs next) (index : ℕ) (hi : index < l.portCount)
    (he : ∀ site, site ≠ index → axes.getD site false = next.getD site false) :
    Relation.ReflTransGen l.OrderedAxisStep axes next := by
  by_cases hs : axes.getD index false = next.getD index false
  · have hall (site : ℕ) : axes.getD site false = next.getD site false := by
      by_cases hi : site = index
      · exact hi ▸ hs
      · exact he site hi
    have hsame := axes_eq_of_reads axes next (ha.axes_length.trans hn.axes_length.symm) hall
    exact hsame ▸ Relation.ReflTransGen.refl
  · have hbit : next.getD index false = !(axes.getD index false) := by
      cases a : axes.getD index false <;> cases b : next.getD index false <;> simp_all
    have hset : next = axes.set index (!(axes.getD index false)) := by
      apply axes_eq_of_reads _ _ (by simp only [List.length_set, ha.axes_length, hn.axes_length])
      intro site
      rw [read_set axes index _ (by rw [ha.axes_length]; exact hi)]
      by_cases hi : site = index
      · simpa only [hi, ite_true] using hbit
      · simp only [hi, ite_false, ← he site hi]
    exact Relation.ReflTransGen.single ⟨ha, index, hi, hset, hn⟩

private theorem other_group_read_set (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    (hlen : axes.length = l.portCount) {first : ℕ} (hgate : .gate .andGate first ∈ l.lowerGroups)
    {group : LowerGroup} (hg : group ∈ l.lowerGroups) (hne : group ≠ .gate .andGate first)
    {index : ℕ} (hi : index ∈ group.shape.ports) (bit : Bool) :
    (axes.set (first + 1) bit).getD index false = axes.getD index false := by
  have hmid : first + 1 < axes.length := by
    rw [hlen]
    exact lower_port_lt l hl hgate (by simp [LowerGroup.shape, PageLevels.Group.ports])
  have hne' : index ≠ first + 1 := by
    intro he
    exact hne (lower_shared l hl hg hgate hi (by simp [LowerGroup.shape, PageLevels.Group.ports, he]))
  rw [read_set axes _ bit hmid, ite_eq_right hne']

/-- Promoting the middle light axis of a supplied-heavy actual AND core preserves all ordered inputs.
-/
theorem OrderedInputs.set_middle_true {l : PortLayout} (hl : l.pages.lowerPage.Valid)
    {axes : List Bool} (ha : l.OrderedInputs axes) {first : ℕ}
    (hgate : .gate .andGate first ∈ l.lowerGroups) (hh : axes.getD (first + 2) false = false) :
    l.OrderedInputs (axes.set (first + 1) true) := by
  have hmid : first + 1 < axes.length := by
    rw [ha.axes_length]
    exact lower_port_lt l hl hgate (by simp [LowerGroup.shape, PageLevels.Group.ports])
  have hother {group : LowerGroup} (hg : group ∈ l.lowerGroups) (hne : group ≠ .gate .andGate first)
      (index : ℕ) (hi : index ∈ group.shape.ports) :=
    other_group_read_set l hl axes ha.axes_length hgate hg hne hi true
  have hheavy : (axes.set (first + 1) true).getD (first + 2) false = false := by
    rw [read_set axes _ true hmid, ite_eq_right (by omega), hh]
  refine ⟨⟨by rw [List.length_set, ha.axes_length], ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b hg
    have keep {index : ℕ} (ht : axes.getD index false = true) :
        (axes.set (first + 1) true).getD index false = true := by
      rw [read_set axes _ true hmid]
      split_ifs <;> first | rfl | exact ht
    exact (ha.upper a b hg).imp keep keep
  · intro a b hg
    have hab := hother hg (by simp)
    rw [hab a (by simp [LowerGroup.shape, PageLevels.Group.ports]),
      hab b (by simp [LowerGroup.shape, PageLevels.Group.ports])]
    exact ha.lower_wire a b hg
  · intro site hg
    have hor := hother hg (by simp)
    rw [hor site (by simp [LowerGroup.shape, PageLevels.Group.ports]),
      hor (site + 1) (by simp [LowerGroup.shape, PageLevels.Group.ports]),
      hor (site + 2) (by simp [LowerGroup.shape, PageLevels.Group.ports])]
    exact ha.or_gate site hg
  · intro site hg
    by_cases he : site = first
    · exact Or.inl (he ▸ hheavy)
    · have hand := hother hg (by intro h; exact he (LowerGroup.gate.inj h).2)
      rw [hand site (by simp [LowerGroup.shape, PageLevels.Group.ports]),
        hand (site + 1) (by simp [LowerGroup.shape, PageLevels.Group.ports]),
        hand (site + 2) (by simp [LowerGroup.shape, PageLevels.Group.ports])]
      exact ha.and_gate site hg
  · intro site hg hm
    by_cases he : site = first
    · subst site
      have ht : (axes.set (first + 1) true).getD (first + 1) false = true := by
        rw [read_set axes _ true hmid, ite_eq_left rfl]
      rw [ht] at hm
      cases hm
    · have hand := hother hg (by intro h; exact he (LowerGroup.gate.inj h).2)
      rw [hand (site + 1) (by simp [LowerGroup.shape, PageLevels.Group.ports])] at hm
      rw [hand site (by simp [LowerGroup.shape, PageLevels.Group.ports])]
      exact ha.and_ordered site hg hm

end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortInputStep
import Mathlib.Data.Bool.Basic

/-! Ordering actual AND light inputs by promoting the middle axis at its original port. -/

public section
namespace PushPuzzle.PushS.PortLayout


private def lowerIndex (l : PortLayout) (group : LowerGroup) (hg : group ∈ l.lowerGroups) :
    l.pages.lowerPage.Index :=
  ⟨l.lowerGroups.idxOf group, by
    simpa only [pages, PageLevels.Pages.lowerPage, List.length_map] using List.idxOf_lt_length_iff.mpr hg⟩

private theorem lowerIndex_group (l : PortLayout) (group : LowerGroup) (hg : group ∈ l.lowerGroups) :
    l.pages.lowerPage.group (lowerIndex l group hg) = group.shape := by
  change (l.lowerGroups.map LowerGroup.shape).get _ = _
  erw [List.get_eq_getElem, List.getElem_map]
  exact congrArg LowerGroup.shape (List.getElem_idxOf (List.idxOf_lt_length_iff.mpr hg))

private theorem lower_bounds (l : PortLayout) (hl : l.pages.lowerPage.Valid)
    {group : LowerGroup} (hg : group ∈ l.lowerGroups) :
    group.shape.left < group.shape.right ∧ group.shape.right < l.portCount := by
  have hb := hl.bounded (lowerIndex l group hg)
  rw [lowerIndex_group l group hg] at hb
  exact hb

private theorem lower_port_lt (l : PortLayout) (hl : l.pages.lowerPage.Valid)
    {group : LowerGroup} (hg : group ∈ l.lowerGroups) {index : ℕ} (hi : index ∈ group.shape.ports) :
    index < l.portCount := by
  have hb := lower_bounds l hl hg
  cases group <;> simp only [LowerGroup.shape, PageLevels.Group.left, PageLevels.Group.right,
    PageLevels.Group.ports, Finset.mem_insert, Finset.mem_singleton] at hb hi <;> omega

private theorem lower_shared (l : PortLayout) (hl : l.pages.lowerPage.Valid)
    {left right : LowerGroup} (ha : left ∈ l.lowerGroups) (hb : right ∈ l.lowerGroups)
    {index : ℕ} (hia : index ∈ left.shape.ports) (hib : index ∈ right.shape.ports) : left = right := by
  obtain ⟨owner, _, ho⟩ := hl.partition index (lower_port_lt l hl ha hia)
  have hi := ho (lowerIndex l left ha) (by
    change index ∈ (l.pages.lowerPage.group (lowerIndex l left ha)).ports
    rw [lowerIndex_group l left ha]
    exact hia)
  have hj := ho (lowerIndex l right hb) (by
    change index ∈ (l.pages.lowerPage.group (lowerIndex l right hb)).ports
    rw [lowerIndex_group l right hb]
    exact hib)
  have he : l.lowerGroups.idxOf left = l.lowerGroups.idxOf right := congrArg Fin.val (hi.trans hj.symm)
  exact (List.idxOf_inj ha).mp he

private def promotion (l : PortLayout) (axes : List Bool) (index : ℕ) : Bool :=
  l.lowerGroups.any fun group => match group with
    | .gate .andGate first => decide (index = first + 1) && axes.getD first false
    | _ => false

private theorem promotion_true (l : PortLayout) (axes : List Bool) (index : ℕ) :
    promotion l axes index = true ↔
      ∃ first, .gate .andGate first ∈ l.lowerGroups ∧ index = first + 1 ∧ axes.getD first false = true := by
  simp only [promotion, List.any_eq_true]
  constructor
  · rintro ⟨group, hg, ht⟩
    cases group with
    | wire a b => cases ht
    | gate kind first =>
      cases kind with
      | andGate =>
        simp only [Bool.and_eq_true, decide_eq_true_eq] at ht
        exact ⟨first, hg, ht.1, ht.2⟩
      | orGate => cases ht
  · rintro ⟨first, hg, hi, ht⟩
    exact ⟨.gate .andGate first, hg, by simpa only [Bool.and_eq_true, decide_eq_true_eq] using And.intro hi ht⟩

private theorem promotion_at_group (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    {group : LowerGroup} (hg : group ∈ l.lowerGroups) {index : ℕ} (hi : index ∈ group.shape.ports) :
    promotion l axes index = true ↔
      ∃ first, group = .gate .andGate first ∧ index = first + 1 ∧ axes.getD first false = true := by
  rw [promotion_true]
  constructor
  · rintro ⟨first, hp, hi', hb⟩
    exact ⟨first, lower_shared l hl hg hp hi (by simp [LowerGroup.shape, PageLevels.Group.ports, hi']), hi', hb⟩
  · rintro ⟨first, rfl, hi', hb⟩
    exact ⟨first, hg, hi', hb⟩

/-- Preserve the same actual port order and set each AND middle axis above its left axis. -/
def orderAxes (l : PortLayout) (axes : List Bool) : List Bool :=
  (List.range l.portCount).map fun index => axes.getD index false || promotion l axes index

/-- The order projection retains the complete original axis allocation. -/
theorem length_orderAxes (l : PortLayout) (axes : List Bool) : (l.orderAxes axes).length = l.portCount := by
  simp only [orderAxes, List.length_map, List.length_range]

private theorem orderAxes_read (l : PortLayout) (axes : List Bool) {index : ℕ} (hi : index < l.portCount) :
    (l.orderAxes axes).getD index false = (axes.getD index false || promotion l axes index) := by
  rw [List.getD_eq_getElem _ _ (by simpa only [length_orderAxes] using hi)]
  simp only [orderAxes, List.getElem_map, List.getElem_range]

private theorem orderAxes_wire (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    {a b index : ℕ} (hg : .wire a b ∈ l.lowerGroups) (hi : index ∈ (.wire a b : LowerGroup).shape.ports) :
    (l.orderAxes axes).getD index false = axes.getD index false := by
  rw [orderAxes_read l axes (lower_port_lt l hl hg hi)]
  have hp : promotion l axes index = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    obtain ⟨first, he, _, _⟩ := (promotion_at_group l hl axes hg hi).mp ht
    cases he
  rw [hp, Bool.or_false]

private theorem promotion_gate (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    {kind : Shuttle.Kind} {first index : ℕ} (hg : .gate kind first ∈ l.lowerGroups)
    (hi : index ∈ (.gate kind first : LowerGroup).shape.ports) :
    promotion l axes index = (if kind = .andGate ∧ index = first + 1 then axes.getD first false else false) := by
  apply Bool.eq_iff_iff.mpr
  rw [promotion_at_group l hl axes hg hi]
  constructor
  · rintro ⟨original, he, hi', ht⟩
    obtain ⟨rfl, rfl⟩ := LowerGroup.gate.inj he
    simp only [hi', and_self, ite_true, ht]
  · intro ht
    split_ifs at ht with h
    exact ⟨first, h.1 ▸ rfl, h.2, ht⟩

private theorem orderAxes_gate (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups) :
    (l.orderAxes axes).getD first false = axes.getD first false ∧
      (l.orderAxes axes).getD (first + 1) false =
        (axes.getD (first + 1) false || if kind = .andGate then axes.getD first false else false) ∧
      (l.orderAxes axes).getD (first + 2) false = axes.getD (first + 2) false := by
  have hread (index : ℕ) (hi : index ∈ (.gate kind first : LowerGroup).shape.ports) :=
    orderAxes_read l axes (lower_port_lt l hl hg hi)
  have hp (index : ℕ) (hi : index ∈ (.gate kind first : LowerGroup).shape.ports) :=
    promotion_gate l hl axes hg hi
  have ha := hread first (by simp [LowerGroup.shape, PageLevels.Group.ports])
  have hb := hread (first + 1) (by simp [LowerGroup.shape, PageLevels.Group.ports])
  have hc := hread (first + 2) (by simp [LowerGroup.shape, PageLevels.Group.ports])
  rw [hp first (by simp [LowerGroup.shape, PageLevels.Group.ports])] at ha
  rw [hp (first + 1) (by simp [LowerGroup.shape, PageLevels.Group.ports])] at hb
  rw [hp (first + 2) (by simp [LowerGroup.shape, PageLevels.Group.ports])] at hc
  have han : first ≠ first + 1 := by omega
  have hcn : first + 2 ≠ first + 1 := by omega
  simp only [han, and_false, ite_false, Bool.or_false] at ha
  simp only [hcn, and_false, ite_false, Bool.or_false] at hc
  simp only [and_true] at hb
  exact ⟨ha, hb, hc⟩

private theorem orderAxes_preserves_true (l : PortLayout) (axes : List Bool)
    (hlen : axes.length = l.portCount) {index : ℕ} (ht : axes.getD index false = true) :
    (l.orderAxes axes).getD index false = true := by
  have hi : index < l.portCount := by
    by_contra hn
    have hdefault := List.getD_eq_default axes false (by omega : axes.length ≤ index)
    rw [hdefault] at ht
    cases ht
  rw [orderAxes_read l axes hi, ht, Bool.true_or]

/-- The actual lower partition makes this order projection legal and ordered at every original gate.
-/
theorem orderAxes_ordered (l : PortLayout) (hl : l.pages.lowerPage.Valid) (axes : List Bool)
    (ha : l.InputLegal axes) : l.OrderedInputs (l.orderAxes axes) := by
  refine ⟨⟨length_orderAxes l axes, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro a b hg
    exact (ha.upper a b hg).imp (orderAxes_preserves_true l axes ha.axes_length)
      (orderAxes_preserves_true l axes ha.axes_length)
  · intro a b hg
    rw [orderAxes_wire l hl axes hg (by simp [LowerGroup.shape, PageLevels.Group.ports]),
      orderAxes_wire l hl axes hg (by simp [LowerGroup.shape, PageLevels.Group.ports])]
    exact ha.lower_wire a b hg
  · intro first hg
    obtain ⟨ha', hb', hc'⟩ := orderAxes_gate l hl axes hg
    simpa only [ha', hb', hc', reduceCtorEq, ite_false, Bool.or_false] using ha.or_gate first hg
  · intro first hg
    obtain ⟨ha', hb', hc'⟩ := orderAxes_gate l hl axes hg
    rw [ha', hb', hc']
    rcases ha.and_gate first hg with hh | ⟨hl, hm⟩
    · exact Or.inl hh
    · exact Or.inr ⟨hl, by simp only [hm, hl, ite_self, Bool.or_false]⟩
  · intro first hg hm
    obtain ⟨ha', hb', _⟩ := orderAxes_gate l hl axes hg
    rw [hb'] at hm
    rw [ha']
    exact (Bool.or_eq_false_iff.mp (by simpa only [ite_true] using hm)).2

/-- The actual order projection fixes every already ordered legal axis array. -/
theorem orderAxes_eq_of_ordered (l : PortLayout) (axes : List Bool) (ha : l.OrderedInputs axes) :
    l.orderAxes axes = axes := by
  apply List.ext_getElem (by rw [length_orderAxes, ha.axes_length])
  intro index hi hj
  have hread := orderAxes_read l axes (by simpa only [length_orderAxes] using hi)
  have hp : promotion l axes index = true → axes.getD index false = true := by
    intro ht
    obtain ⟨first, hg, rfl, hleft⟩ := (promotion_true l axes index).mp ht
    cases hm : axes.getD (first + 1) false with
    | false => exact False.elim (by have h := ha.and_ordered first hg hm; rw [h] at hleft; cases hleft)
    | true => rfl
  have he : (axes.getD index false || promotion l axes index) = axes.getD index false := by
    cases hraw : axes.getD index false <;> cases hprom : promotion l axes index <;> first
      | rfl
      | exact False.elim (by have h := hp hprom; rw [hraw] at h; cases h)
  rw [he, List.getD_eq_getElem _ _ hj] at hread
  rwa [List.getD_eq_getElem _ _ hi] at hread

end PushPuzzle.PushS.PortLayout

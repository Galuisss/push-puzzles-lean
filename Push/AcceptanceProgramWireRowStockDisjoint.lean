/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockFixed
import all Push.AcceptanceProgramWireRowStockSlots
import all PushS.PortWireIndexing
import all PushS.PortWireGeometry
import all PushS.PortSegments

/-! Entire open WIRE rails on one actual page and level are pairwise disjoint. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout PageLevels

private theorem ordinary_same_left (l : PortLayout) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) (hgw : g.gate = none)
    (hh : h ∈ placements l) (hhw : h.gate = none)
    (hs : g.side = h.side) (hx : g.left = h.left) : g = h := by
  have he := l.endpoints_key_injective hl (wire_endpoints l hg hgw).1 (wire_endpoints l hh hhw).1 hs hx
  have hi : g.internal = h.internal := congrArg Endpoint.internal he
  apply first_slot_owner l hg hh hi.le
  simp only [slotCount, hgw, Option.isSome_none, Bool.false_eq_true, ite_false]
  omega

private theorem ordinary_intervals_disjoint (l : PortLayout) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) (hgw : g.gate = none)
    (hh : h ∈ placements l) (hhw : h.gate = none)
    (hs : g.side = h.side) (hlevel : g.level = h.level) (hne : g ≠ h) :
    g.right < h.left ∨ h.right < g.left := by
  obtain ⟨i, hi, hil⟩ := wire_owner l hg hgw
  have hhowner : ∃ k : (pageFor l g.side).Index,
      (pageFor l g.side).group k = .wire h.left h.right ∧ levelFor l g.side k = h.level := by
    rw [hs]
    exact wire_owner l hh hhw
  obtain ⟨k, hk, hkl⟩ := hhowner
  have hik : i ≠ k := by
    intro he
    subst k
    have hx : g.left = h.left := (Group.wire.inj (hi.symm.trans hk)).1
    exact hne (ordinary_same_left l hl hg hgw hh hhw hs hx)
  rcases (pageFor_valid l hl g.side).noncrossing i k hik with hleft | hright | hnest | hnest
  · left
    rwa [hi, hk] at hleft
  · right
    rwa [hi, hk] at hright
  · have hlt := levelFor_parent_gt l hl g.side hnest
    rw [hil, hkl] at hlt
    omega
  · have hlt := levelFor_parent_gt l hl g.side hnest
    rw [hil, hkl] at hlt
    omega

/-- The full physical open rails of distinct actual ordinary WIREs on the same page and level are disjoint. -/
theorem wire_row_rails_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) (hgw : g.gate = none)
    (hh : h ∈ placements l) (hhw : h.gate = none)
    (hs : g.side = h.side) (hlevel : g.level = h.level) (hne : g ≠ h) :
    Disjoint (wireOpenRail p g) (wireOpenRail p h) := by
  apply Finset.disjoint_left.mpr
  intro q hqg hqh
  have hqg := (Finset.mem_filter.mp hqg).2.2
  have hqh := (Finset.mem_filter.mp hqh).2.2
  rcases ordinary_intervals_disjoint l hl hg hgw hh hhw hs hlevel hne with hg | hh
  · have hsep := axis_spacing p hg
    omega
  · have hsep := axis_spacing p hh
    omega

/-- The actual finite work-row placement set supplies pairwise disjoint whole rails. -/
theorem wireRowPlacements_rails_pairwise (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) (j : ℕ) :
    Set.PairwiseDisjoint (↑(wireRowPlacements l side j)) (wireOpenRail p) := by
  classical
  intro g hg h hh hne
  obtain ⟨hg, hgw, hgs, hgl⟩ := Finset.mem_filter.mp hg
  obtain ⟨hh, hhw, hhs, hhl⟩ := Finset.mem_filter.mp hh
  exact wire_row_rails_disjoint l p hl (List.mem_toFinset.mp hg) hgw (List.mem_toFinset.mp hh) hhw
    (hgs.trans hhs.symm) (hgl.trans hhl.symm) hne

/-- Every actual placement work row occurs in the real R23 whole-row request set. -/
theorem wire_work_row_requested (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) :
    wireWorkRow p g.side g.level ∈ workRows l p \ ({0, p.H} ∪ probeRows l p) := by
  obtain ⟨hj, hjM⟩ := placement_level_bounds l hl hg
  have hjm := hjM.trans hM
  apply Finset.mem_sdiff.mpr
  refine ⟨(level_work_rows l p g.side hj hjm).1, ?_⟩
  intro h
  rcases Finset.mem_union.mp h with hf | hp
  · have hY := readDepth_ge p hj hjm
    have hD := readDepth_add_lt_D p g.level
    rw [readDepth_eq p hj hjm] at hY hD
    have hH : p.H = 2 * p.D := rfl
    simp only [Finset.mem_insert, Finset.mem_singleton, wireWorkRow] at hf
    cases hs : g.side <;> simp only [hs, ite_true, reduceCtorEq, ite_false] at hf <;> omega
  · exact wireWorkRow_not_probe l p hl hM g.side hj hjm hp

end PushPuzzle.Push.AcceptanceProgram

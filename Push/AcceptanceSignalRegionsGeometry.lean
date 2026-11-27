/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSignalRegions
import all Push.AcceptanceProgramWireRowStockPartition
import all PushS.PortWireIndexing
import all PushS.PortWireGeometry
import all PushS.PortGateIndexing
import all PushS.PortAxisFixed
import all PushS.PortSegments
import all PushS.PortEndpointCrossing
import all PushS.PortAxisMacro
import all PushS.PortGateRail

/-! The actual open axes and same-level placement intervals form separated physical regions. -/

public section
namespace PushPuzzle.Push.AcceptanceSignalRegions

open PushFS PushFS.Reduction PushS PushS.PortLayout PageLevels SegmentRecipe

private theorem placement_owner (l : PortLayout) {g : Placement} (hg : g ∈ placements l) :
    ∃ i : (pageFor l g.side).Index, ((pageFor l g.side).group i).left = g.left ∧
      ((pageFor l g.side).group i).right = g.right ∧ levelFor l g.side i = g.level := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, k⟩, hk, rfl⟩ | ⟨⟨lower, k⟩, hk, rfl⟩
  · let i : Fin l.upperPairs.length := ⟨k, by simpa using List.snd_lt_of_mem_zipIdx hk⟩
    refine ⟨⟨i.val, by simpa only [pageFor, pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩,
      ?_, ?_, (upperLevel_index l i).symm⟩
    · exact congrArg Group.left (upper_group_at l hk)
    · exact congrArg Group.right (upper_group_at l hk)
  · cases lower with
    | wire a b =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl]
      let i : Fin l.lowerGroups.length := ⟨k, by simpa using List.snd_lt_of_mem_zipIdx hk⟩
      refine ⟨⟨i.val, by simpa only [pageFor, pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩,
        ?_, ?_, (lowerLevel_index l i).symm⟩
      · exact congrArg Group.left (lower_group_at l hk)
      · exact congrArg Group.right (lower_group_at l hk)
    | gate kind first =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr]
      let i : Fin l.lowerGroups.length := ⟨k, by simpa using List.snd_lt_of_mem_zipIdx hk⟩
      refine ⟨⟨i.val, by simpa only [pageFor, pages, Pages.upperPage, Pages.lowerPage, List.length_map] using i.isLt⟩,
        ?_, ?_, (lowerLevel_index l i).symm⟩
      · exact congrArg Group.left (lower_group_at l hk)
      · exact congrArg Group.right (lower_group_at l hk)

private theorem placement_same_left (l : PortLayout) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) (hh : h ∈ placements l)
    (hs : g.side = h.side) (hx : g.left = h.left) : g = h := by
  have he := l.endpoints_key_injective hl (placement_endpoints l hg).1 (placement_endpoints l hh).1 hs hx
  have hi : g.internal = h.internal := congrArg Endpoint.internal he
  exact first_slot_owner l hg hh (by omega) (by dsimp only [slotCount]; split <;> omega)

private theorem placement_intervals_disjoint (l : PortLayout) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) (hh : h ∈ placements l)
    (hs : g.side = h.side) (hlevel : g.level = h.level) (hne : g ≠ h) :
    g.right < h.left ∨ h.right < g.left := by
  obtain ⟨i, hil, hir, hi⟩ := placement_owner l hg
  have ho := placement_owner l hh
  rw [← hs] at ho
  obtain ⟨k, hkl, hkr, hk⟩ := ho
  have hik : i ≠ k := by
    intro he
    subst k
    exact hne (placement_same_left l hl hg hh hs (hil.symm.trans hkl))
  rcases (pageFor_valid l hl g.side).noncrossing i k hik with hleft | hright | hnest | hnest
  · exact Or.inl (by simpa only [hir, hkl] using hleft)
  · exact Or.inr (by simpa only [hkr, hil] using hright)
  · have hlt := levelFor_parent_gt l hl g.side hnest
    rw [hi, hk] at hlt
    omega
  · have hlt := levelFor_parent_gt l hl g.side hnest
    rw [hi, hk] at hlt
    omega

private theorem railRegion_eq_wireOpenRail (l : PortLayout) (p : Scales.Parameters)
    {g : Placement} (hg : g ∈ placements l) : railRegion p g = wireOpenRail p g := by
  cases hk : g.gate with
  | none => simp only [railRegion, hk]
  | some kind =>
    have hs := (placement_gate_shape l hg hk).1
    have hj := gate_level_one l hg hk
    simp only [railRegion, hk, wireOpenRail, gateOpenRail, hs, hj, reduceCtorEq, ite_false]

private theorem equal_work_rows (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) {q : Cell (p.W + 1) (p.H + 1)}
    (hqg : q ∈ wireOpenRail p g) (hqh : q ∈ wireOpenRail p h) :
    g.side = h.side ∧ g.level = h.level := by
  have hgy := (Finset.mem_filter.mp hqg).2.1
  have hhy := (Finset.mem_filter.mp hqh).2.1
  have hgD := readDepth_add_lt_D p g.level
  have hhD := readDepth_add_lt_D p h.level
  have hH : p.H = 2 * p.D := rfl
  have hs : g.side = h.side := by
    cases gs : g.side <;> cases hs : h.side <;>
      simp only [gs, hs, reduceCtorEq, ite_true, ite_false] at hgy hhy ⊢ <;> omega
  refine ⟨hs, ?_⟩
  obtain ⟨hg0, hgM⟩ := placement_level_bounds l hl hg
  obtain ⟨hh0, hhM⟩ := placement_level_bounds l hl hh
  have hgM := hgM.trans hM
  have hhM := hhM.trans hM
  rw [← hs] at hhy
  have hdepth : readDepth p g.level = readDepth p h.level := by
    cases gs : g.side <;> simp only [gs, ite_true, reduceCtorEq, ite_false] at hgy hhy <;> omega
  rcases lt_trichotomy g.level h.level with hlt | heq | hlt
  · have := depth_gap p hg0 hlt hhM
    omega
  · exact heq
  · have := depth_gap p hh0 hlt hgM
    omega

/-- Distinct actual placement rails are disjoint, including the three-port rails. -/
theorem railRegion_pairwise (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) (hne : g ≠ h) :
    Disjoint (railRegion p g) (railRegion p h) := by
  rw [railRegion_eq_wireOpenRail l p hg, railRegion_eq_wireOpenRail l p hh]
  apply Finset.disjoint_left.mpr
  intro q hqg hqh
  obtain ⟨hs, hlevel⟩ := equal_work_rows l p hl hM hg hh hqg hqh
  have hqg := (Finset.mem_filter.mp hqg).2.2
  have hqh := (Finset.mem_filter.mp hqh).2.2
  rcases placement_intervals_disjoint l hl hg hh hs hlevel hne with hg | hh
  · have := axis_spacing p hg
    omega
  · have := axis_spacing p hh
    omega

/-- Every point in an indexed axis has the corresponding literal horizontal coordinate. -/
theorem axisRegion_column (l : PortLayout) (p : Scales.Parameters) (i : Fin l.portCount)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ axisRegion l p i) : q.1.val = p.x i.val := by
  unfold axisRegion at hq
  split at hq <;> exact (Finset.mem_filter.mp hq).2.1

/-- Different numbered axes have disjoint entire regions. -/
theorem axisRegion_pairwise (l : PortLayout) (p : Scales.Parameters)
    {i j : Fin l.portCount} (hne : i ≠ j) : Disjoint (axisRegion l p i) (axisRegion l p j) := by
  apply Finset.disjoint_left.mpr
  intro q hi hj
  have heq := (axisRegion_column l p i hi).symm.trans (axisRegion_column l p j hj)
  have hd := p.outer_distance
  have hv : i.val = j.val := by
    by_contra h
    rcases lt_or_gt_of_ne h with h | h
    all_goals have := axis_spacing p h; omega
  exact hne (Fin.ext hv)

/-- No literal fixed hole lies in an indexed open axis. -/
theorem fixedHoles_axisRegion_disjoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (i : Fin l.portCount) : Disjoint (fixedHoles l p) (axisRegion l p i) := by
  apply Finset.disjoint_left.mpr
  intro q hf ha
  have hx := axisRegion_column l p i ha
  have hraw := (finite_mem p _ q).mp hf
  have hsource := l.fixedSegments_on_main_axis p hl hM haxes i.isLt hraw hx
  unfold axisRegion at ha
  split at ha
  · have ha := (Finset.mem_filter.mp ha).2
    have hY := readDepth_ge p le_rfl p.levels_pos
    rcases hsource with h0 | hH | ⟨_, hhalf⟩ <;> omega
  · rename_i hi
    have ha := (Finset.mem_filter.mp ha).2
    rcases hsource with h0 | hH | ⟨hgate, _⟩
    · omega
    · omega
    · exact hi hgate

/-- No literal fixed hole lies in an actual placement's open rail. -/
theorem fixedHoles_railRegion_disjoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    {g : Placement} (hg : g ∈ placements l) :
    Disjoint (fixedHoles l p) (railRegion p g) := by
  cases hk : g.gate with
  | none =>
    simpa only [fixedHoles, railRegion, hk] using
      AcceptanceProgram.wire_fixed_disjoint l p hl hM haxes [] hg hk
  | some kind =>
    simp only [railRegion, hk]
    apply Finset.disjoint_left.mpr
    intro q hf hr
    have hencoded : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p (l.canonical [])) := by
      obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hf
      exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩
    have hnear : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (gateHorizontalSegments p (l.canonical []) g kind) := by
      rw [← l.encodedSegments_gateOpenRail p hl hM haxes (l.canonical []) hg hk]
      exact Finset.mem_inter.mpr ⟨hencoded, hr⟩
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hnear
    have hsignal := (mem_pointHoles _ _).mpr
      ⟨s, gateHorizontalSegments_mem_signal l p (l.canonical []) hg hk hs, hc⟩
    exact Finset.disjoint_left.mp (l.fixedSegments_disjoint_signalSegments p hl hM haxes (l.canonical []))
      ((finite_mem p _ q).mp hf) hsignal

end PushPuzzle.Push.AcceptanceSignalRegions

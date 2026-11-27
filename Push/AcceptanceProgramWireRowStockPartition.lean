/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStockGeometry
import all PushS.PortFixedSeparation
import all PushS.PortWireRail
import all PushS.PortWireIndexing
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! The actual R23 row splits into fixed stock and the surviving stocks of its ordinary WIREs. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe
open scoped BigOperators

/-- The actual ordinary placements allocated to one page and working level. -/
@[expose] noncomputable def wireRowPlacements (l : PortLayout) (side : Side) (j : ℕ) : Finset Placement := by
  classical
  exact (placements l).toFinset.filter fun g => g.gate = none ∧ g.side = side ∧ g.level = j

/-- Target-independent fixed geometry left on this work row by the actual R23 mask. -/
@[expose] def wireRowFixedStock (l : PortLayout) (p : Scales.Parameters) (side : Side) (j : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  ((emit (wireWorkPrefix l p []) (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p))).remaining).filter
    fun q => q.2.val = wireWorkRow p side j

private theorem wireNear_signal (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p state g) ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.signalSegments p state) := by
  intro q hq
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  refine (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ ?_, hc⟩
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  rcases List.mem_append.mp hs with hs | hs
  · exact List.mem_flatMap.mpr ⟨wireLeft g, heL, List.mem_of_mem_drop hs⟩
  · exact List.mem_flatMap.mpr ⟨wireRight g, heR, List.mem_of_mem_drop hs⟩

/-- The literal fixed source contributes no holes inside an ordinary open rail. -/
theorem wire_fixed_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    Disjoint (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p)) (wireOpenRail p g) := by
  apply Finset.disjoint_left.mpr
  intro q hf hr
  have ht : q ∈ targetHoles l p target := by
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hf
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩
  have hn := wireNear_signal l p (l.canonical target) hg hw
    (show q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p (l.canonical target) g) from
      by rw [← l.encodedSegments_wireOpenRail p hl hM haxes (l.canonical target) hg hw]; exact Finset.mem_inter.mpr ⟨ht, hr⟩)
  exact Finset.disjoint_left.mp (l.fixedSegments_disjoint_signalSegments p hl hM haxes (l.canonical target))
    ((finite_mem p _ q).mp hf) ((finite_mem p _ q).mp hn)

private theorem wireNear_endpoint (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireNearSegments p state g)) :
    ∃ e ∈ l.endpoints, e.side = g.side ∧ e.internal = g.internal ∧
      (q.1.val, q.2.val) ∈ pointHoles ((endpointSegments (coordinates p) state e).drop 1) := by
  have hq := (finite_mem p _ q).mp hq
  rw [wireNearSegments, pointHoles_append] at hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact ⟨wireLeft g, (wire_endpoints l hg hw).1, rfl, rfl, hq⟩
  · exact ⟨wireRight g, (wire_endpoints l hg hw).2, rfl, by simp [wireRight], hq⟩

/-- Distinct ordinary placements on one page have disjoint canonical receiving stocks. -/
theorem wire_target_rails_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g h : Placement} (hg : g ∈ placements l) (hgw : g.gate = none)
    (hh : h ∈ placements l) (hhw : h.gate = none) (hs : g.side = h.side) (hne : g ≠ h) :
    Disjoint (targetHoles l p target ∩ wireOpenRail p g) (targetHoles l p target ∩ wireOpenRail p h) := by
  change Disjoint (SegmentRecipe.holes _ _ (l.encodedSegments p (l.canonical target)) ∩ wireOpenRail p g)
    (SegmentRecipe.holes _ _ (l.encodedSegments p (l.canonical target)) ∩ wireOpenRail p h)
  rw [l.encodedSegments_wireOpenRail p hl hM haxes (l.canonical target) hg hgw,
    l.encodedSegments_wireOpenRail p hl hM haxes (l.canonical target) hh hhw]
  apply Finset.disjoint_left.mpr
  intro q hqg hqh
  obtain ⟨e, he, hes, hei, hqe⟩ := wireNear_endpoint l p (l.canonical target) hg hgw hqg
  obtain ⟨f, hf, hfs, hfi, hqf⟩ := wireNear_endpoint l p (l.canonical target) hh hhw hqh
  have hp : e.port = f.port := by
    rcases lt_trichotomy e.port f.port with hp | hp | hp
    · exact False.elim (Finset.disjoint_left.mp (endpointHorizontals_disjoint p (l.canonical target) e f hp) hqe hqf)
    · exact hp
    · exact False.elim (Finset.disjoint_left.mp (endpointHorizontals_disjoint p (l.canonical target) f e hp) hqf hqe)
  have hef := l.endpoints_key_injective hl he hf (hes.trans (hs.trans hfs.symm)) hp
  have hint : g.internal = h.internal := hei.symm.trans ((congrArg Endpoint.internal hef).trans hfi)
  apply hne
  apply first_slot_owner l hg hh (by omega)
  simp only [slotCount, hgw, Option.isSome_none, Bool.false_eq_true, ite_false]
  omega

/-- Every actual selected work row is exactly its fixed residual and the residual ordinary rails. -/
theorem wireWork_row_eq (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (hordinary : side = .upper ∨ 2 ≤ j) :
    (wireWorkReference l p target).filter (fun q => q.2.val = wireWorkRow p side j) =
      wireRowFixedStock l p side j ∪ (wireRowPlacements l side j).biUnion
        (fun g => wireWorkReference l p target ∩ wireOpenRail p g) := by
  classical
  have hpref := wireWorkPrefix_eq l p hl hM haxes target
  ext q
  constructor
  · rintro hq
    obtain ⟨hq, hy⟩ := Finset.mem_filter.mp hq
    have ht := emit_remaining_subset _ _ hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp ht
    rcases List.mem_append.mp hs with hs | hs
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨?_, hy⟩
      rw [emit_remaining]
      exact Finset.mem_sdiff.mpr ⟨(SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩,
        hpref ▸ (Finset.mem_sdiff.mp (by simpa only [wireWorkReference, emit_remaining] using hq)).2⟩
    · obtain ⟨g, hg, hw, hside, hjg, hr⟩ := wireWork_signal_rail l p hl hM target side hj hjm hordinary hq hy
        ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨g, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hg, hw, hside, hjg⟩, Finset.mem_inter.mpr ⟨hq, hr⟩⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hf | hr
    · obtain ⟨hf, hy⟩ := Finset.mem_filter.mp hf
      obtain ⟨hf, hmask⟩ := Finset.mem_sdiff.mp (by simpa only [emit_remaining] using hf)
      obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hf
      apply Finset.mem_filter.mpr
      refine ⟨?_, hy⟩
      rw [wireWorkReference, emit_remaining, hpref]
      exact Finset.mem_sdiff.mpr ⟨(SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩, hmask⟩
    · obtain ⟨g, hg, hq⟩ := Finset.mem_biUnion.mp hr
      obtain ⟨_, hw, hs, hjg⟩ := Finset.mem_filter.mp hg
      obtain ⟨hq, hr⟩ := Finset.mem_inter.mp hq
      have hy := (Finset.mem_filter.mp hr).2.1
      rw [hs, hjg, readDepth_eq p hj hjm] at hy
      exact Finset.mem_filter.mpr ⟨hq, hy⟩

end PushPuzzle.Push.AcceptanceProgram

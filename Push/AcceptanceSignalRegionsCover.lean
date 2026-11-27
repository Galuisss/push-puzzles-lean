/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSignalRegionsGeometry
import all PushS.PortOrdinaryAxis
import all PushS.PortGateAxis
import all PushS.PortGateRail
import all PushS.PortWireRail
import all PushS.PortAxisMacro
import all PushS.PortEndpointCrossing
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortSegments
import all PushS.PortWireIndexing
import all PushS.PortGateIndexing

/-! Literal signal emission is covered by the actual finite axis and rail family. -/

public section
namespace PushPuzzle.Push.AcceptanceSignalRegions

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem endpoint_axis_region (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {e : Endpoint} (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      ((endpointSegments (coordinates p) state e).take 1)) :
    q ∈ axisRegion l p ⟨e.port, l.endpoints_port_lt hl he⟩ := by
  have hr := axis_near_inside l p hl hM state e he hq
  unfold axisRegion
  split
  · rename_i hi
    have hs : e.side = .upper := by
      cases hs : e.side with
      | upper => rfl
      | lower =>
        obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
        exact (l.endpoints_lower_ne_gate_middle hl hg he hs hm).elim
    obtain ⟨s, hmem, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    have hpage := signal_endpoint_page p state e
      ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_take hmem, hc⟩)
    have hD := readDepth_add_lt_D p 1
    have hH : p.H = 2 * p.D := rfl
    simp only [hs, ite_true] at hpage
    have hr := (Finset.mem_filter.mp hr).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hr.1, hr.2.1, by omega⟩
  · exact hr

private theorem endpoint_horizontal_region (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles ((endpointSegments (coordinates p) state e).drop 1)) :
    ∃ g ∈ placements l, q ∈ railRegion p g := by
  obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
  cases hk : g.gate with
  | none =>
    refine ⟨g, hg, ?_⟩
    simp only [railRegion, hk]
    apply wire_near_subset_rail l p hl state hg hk
    apply (finite_mem p _ q).mpr
    rw [wireNearSegments, pointHoles_append]
    simp only [hk, Option.isSome_none, Bool.false_eq_true, ite_false, Nat.add_zero,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Finset.mem_union_left _ hq
    · exact Finset.mem_union_right _ hq
  | some kind =>
    refine ⟨g, hg, ?_⟩
    simp only [railRegion, hk]
    apply gateHorizontalSegments_subset_rail l p hl state hg hk
    apply (finite_mem p _ q).mpr
    rw [gateHorizontalSegments, pointHoles_append, pointHoles_append]
    simp only [hk, Option.isSome_some, ite_true, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hq)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hq)

private theorem gate_core_axis_region (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles ((gateSegments (coordinates p) state kind g.left g.internal).drop 2)) :
    ∃ i : Fin l.portCount, q ∈ axisRegion l p i := by
  have hgate := placement_gate_mem l hg hk
  have hi : g.left + 1 ∈ l.gateCenterCoordinates := center_of_gate l hgate
  have hmid := gate_middle_lt l hl hgate
  obtain ⟨upper, hu, hs, hp⟩ := l.endpoints_upper_exists hl hmid
  refine ⟨⟨g.left + 1, hmid⟩, ?_⟩
  simp only [axisRegion, hi, ite_true]
  apply gate_axis_near_inside l p hl hM state kind g.left g.internal upper hu hs hp
  apply (finite_mem p _ q).mpr
  rw [gateAxisSegments, pointHoles_append]
  exact Finset.mem_union_right _ hq

/-- Every literal signal hole belongs to an actual numbered axis or actual placement rail. -/
theorem signal_subset_regions (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.signalSegments p state) ⊆
      Finset.univ.biUnion (region l p) := by
  classical
  intro q hq
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    have hp := (mem_pointHoles _ _).mpr ⟨s, hs, hc⟩
    rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state e), pointHoles_append] at hp
    rcases Finset.mem_union.mp hp with ha | hh
    · exact Finset.mem_biUnion.mpr ⟨.inl ⟨e.port, l.endpoints_port_lt hl he⟩, Finset.mem_univ _,
        endpoint_axis_region l p hl hM state he ((finite_mem p _ q).mpr ha)⟩
    · obtain ⟨g, hg, hrail⟩ := endpoint_horizontal_region l p hl state he hh
      exact Finset.mem_biUnion.mpr ⟨.inr ⟨g, List.mem_toFinset.mpr hg⟩, Finset.mem_univ _, hrail⟩
  · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
    cases hk : g.gate with
    | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
    | some kind =>
      have hp := (mem_pointHoles _ _).mpr
        ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩
      rw [← List.take_append_drop 2 (gateSegments (coordinates p) state kind g.left g.internal), pointHoles_append] at hp
      rcases Finset.mem_union.mp hp with hh | ha
      · have hr : q ∈ railRegion p g := by
          simp only [railRegion, hk]
          apply gateHorizontalSegments_subset_rail l p hl state hg hk
          apply (finite_mem p _ q).mpr
          rw [gateHorizontalSegments, pointHoles_append]
          exact Finset.mem_union_right _ hh
        exact Finset.mem_biUnion.mpr ⟨.inr ⟨g, List.mem_toFinset.mpr hg⟩, Finset.mem_univ _, hr⟩
      · obtain ⟨i, hi⟩ := gate_core_axis_region l p hl hM state hg hk ha
        exact Finset.mem_biUnion.mpr ⟨.inl i, Finset.mem_univ _, hi⟩

/-- The canonical initial holes are covered by the fixed stock and the indexed signal-region stocks. -/
theorem initial_holes_cover (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) :
    PushS.holes (l.canonicalInstance p hl hM haxes initial target).initial =
      fixedHoles l p ∪ Finset.univ.biUnion
        (fun i : RegionIndex l => PushS.holes (l.canonicalInstance p hl hM haxes initial target).initial ∩ region l p i) := by
  classical
  let I := l.canonicalInstance p hl hM haxes initial target
  have hinit : (PushS.holes I.initial : Finset (Cell (p.W + 1) (p.H + 1))) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial)) :=
    l.physicalInstance_initial_holes p hl hM haxes (l.canonical initial) (l.canonical target)
  apply Finset.Subset.antisymm
  · intro q hq
    have hraw := hinit ▸ hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hraw
    rcases List.mem_append.mp hs with hf | hs
    · exact Finset.mem_union_left _ ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hf, hc⟩)
    · have hsig := signal_subset_regions l p hl hM (l.canonical initial)
        ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
      obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hsig
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, Finset.mem_inter.mpr ⟨hq, hi⟩⟩)
  · intro q hq
    rcases Finset.mem_union.mp hq with hf | hs
    · change q ∈ (PushS.holes I.initial : Finset (Cell (p.W + 1) (p.H + 1)))
      rw [hinit]
      obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hf
      exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hc⟩
    · obtain ⟨_, _, hi⟩ := Finset.mem_biUnion.mp hs
      exact (Finset.mem_inter.mp hi).1

end PushPuzzle.Push.AcceptanceSignalRegions

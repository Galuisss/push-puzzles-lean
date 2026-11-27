/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateIndexing
public import PushS.ShuttleMacroSegments
public import PushS.PortGatePageWindow
public import PushS.PortFixedSeparation
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortAxisMacro
import all PushS.PortGatePageWindow
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortSegments

/-! The actual complete marked board performs the core's five-push short-train switch. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe ShuttleMacro

private def gateRest (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (g : Placement) : List Segment :=
  l.fixedSegments p ++ (l.endpoints.flatMap (endpointSegments (coordinates p) state) ++
    ((placements l).filter fun h => decide (h.internal ≠ g.internal)).flatMap
      (tripleSignal (coordinates p) state))

private theorem core_signal_mem (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind g.left g.internal)) :
    q ∈ pointHoles (l.signalSegments p state) := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
  exact (mem_pointHoles _ q).mpr ⟨s, List.mem_append_right _
    (List.mem_flatMap.mpr ⟨g, hg, by simpa only [tripleSignal, hk, Option.elim_some] using hs⟩), hc⟩

private theorem gateRest_set_short (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (b : Bool) : gateRest l p (withShort state g.internal b) g = gateRest l p state g := by
  unfold gateRest
  congr 2
  · apply List.flatMap_congr
    intro e he
    have hn := gate_short_endpoint_internal l hg hk he
    simp only [endpointSegments, withShort, List.getD, List.getElem?_set_ne hn.symm]
  · apply List.flatMap_congr
    intro h hh
    obtain ⟨hh, hne⟩ := List.mem_filter.mp hh
    have hne : h.internal ≠ g.internal := of_decide_eq_true hne
    cases hhk : h.gate with
    | none => simp only [tripleSignal, hhk, Option.elim_none]
    | some other =>
      have h0 := gate_other_internal l hg hk hh hhk hne (i := 1) (j := 0) (by omega) (by omega)
      have h1 := gate_other_internal l hg hk hh hhk hne (i := 1) (j := 1) (by omega) (by omega)
      have h2 := gate_other_internal l hg hk hh hhk hne (i := 1) (j := 2) (by omega) (by omega)
      simp only [Nat.add_zero] at h0
      simp only [tripleSignal, hhk, Option.elim_some, gateSegments, withShort, List.getD,
        List.getElem?_set_ne h0.symm, List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
      rfl

private theorem gate_signal_split (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    pointHoles ((placements l).flatMap (tripleSignal (coordinates p) state)) =
      pointHoles (((placements l).filter fun h => decide (h.internal ≠ g.internal)).flatMap
        (tripleSignal (coordinates p) state)) ∪
      pointHoles (gateSegments (coordinates p) state kind g.left g.internal) := by
  ext q
  constructor
  · intro hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨h, hh, hs⟩ := List.mem_flatMap.mp hs
    by_cases hne : h.internal ≠ g.internal
    · exact Finset.mem_union_left _ ((mem_pointHoles _ q).mpr ⟨s, List.mem_flatMap.mpr
        ⟨h, List.mem_filter.mpr ⟨hh, decide_eq_true hne⟩, hs⟩, hc⟩)
    · have heq : g = h := first_slot_owner l hg hh (by omega) (by
        simp only [slotCount, hk, Option.isSome_some, ite_true]
        omega)
      subst h
      exact Finset.mem_union_right _ ((mem_pointHoles _ q).mpr
        ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hq | hq
    · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
      obtain ⟨h, hh, hs⟩ := List.mem_flatMap.mp hs
      exact (mem_pointHoles _ q).mpr ⟨s, List.mem_flatMap.mpr
        ⟨h, (List.mem_filter.mp hh).1, hs⟩, hc⟩
    · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
      exact (mem_pointHoles _ q).mpr ⟨s, List.mem_flatMap.mpr
        ⟨g, hg, by simpa only [tripleSignal, hk, Option.elim_some] using hs⟩, hc⟩

private theorem gate_full_split (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateRest l p state g) ∪
        coreHoles p state kind g.left g.internal := by
  ext q
  simp only [coreHoles, finite_mem, encodedSegments, signalSegments, rawSignals, gateRest,
    pointHoles_append, Finset.mem_union]
  rw [gate_signal_split l p state hg hk, Finset.mem_union]
  tauto

private theorem core_window_page (l : PortLayout) (p : Scales.Parameters)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (ha : g.left + 1 < p.axes) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (coreRail p g.left ha).window) :
    g.left + 1 ∈ l.gateCenterCoordinates ∧ q ∈ gatePageWindow p (g.left + 1) := by
  have hi := center_of_gate l (placement_gate_mem l hg hk)
  have hw := ((coreRail p g.left ha).mem_window_iff q).mp hq
  have hy := congrArg Fin.val hw.1
  change q.2.val = p.H - readDepth p 1 at hy
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  refine ⟨hi, ⟨by omega, by omega⟩, ?_⟩
  have hx := ((coreRail p g.left ha).mem_window_iff q).mp hq
  change _ ∧ p.x (g.left + 1) + 1 ≤ q.1.val ∧ q.1.val ≤ p.x (g.left + 1) + 9 at hx
  simp only [Nat.dist]
  omega

private theorem gate_rest_window_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (ha : g.left + 1 < p.axes)
    (hi : g.internal + 1 < state.internal.length) :
    Disjoint (SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateRest l p state g))
      (coreRail p g.left ha).window := by
  apply Finset.disjoint_left.mpr
  intro q hrest hwin
  obtain ⟨hcenter, hpage⟩ := core_window_page l p hg hk ha hwin
  have hrest := (finite_mem p _ q).mp hrest
  simp only [gateRest, pointHoles_append, Finset.mem_union] at hrest
  rcases hrest with hfixed | hend | hother
  · have hnot (b : Bool) : q ∉ coreHoles p (withShort state g.internal b) kind g.left g.internal := by
      intro hq
      exact Finset.disjoint_left.mp
        (l.fixedSegments_disjoint_signalSegments p hl hM haxes (withShort state g.internal b)) hfixed
        (core_signal_mem l p _ hg hk ((finite_mem p _ q).mp hq))
    have hpair (b : Bool) : q ∈ (coreRail p g.left ha).pair (if b then 5 else 0) := by
      by_contra hn
      exact hnot b ((coreHoles_window p state kind g.left g.internal ha hi b q hwin).mpr hn)
    have h0 := hpair false
    have h5 := hpair true
    simp only [Bool.false_eq_true, ite_false, ite_true, Rail.pair, Rail.cell, coreRail,
      Finset.mem_insert, Finset.mem_singleton, Prod.ext_iff, Fin.ext_iff] at h0 h5
    omega
  · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hend
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact gate_window_no_endpoint l p hl state hcenter hpage e he
      (Or.inr ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩))
  · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hother
    obtain ⟨h, hh, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨hh, hne⟩ := List.mem_filter.mp hh
    have hne : h.internal ≠ g.internal := of_decide_eq_true hne
    cases hhgate : h.gate with
    | none => simp only [tripleSignal, hhgate, Option.elim_none, List.not_mem_nil] at hs
    | some other =>
      have hspan := gate_signal_span p state other h.left h.internal
        ((mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hhgate, Option.elim_some] using hs, hc⟩)
      have hport : h.left + 1 = g.left + 1 := nearby_axis_eq p hpage.2 (by omega)
      have hgside := (placement_gate_shape l hg hk).1
      have hhside := (placement_gate_shape l hh hhgate).1
      have heq := l.endpoints_key_injective hl (placement_endpoints l hg).1 (placement_endpoints l hh).1
        (hgside.trans hhside.symm) (by change g.left = h.left; omega)
      exact hne (congrArg Endpoint.internal heq).symm

/-- Five genuine eastward pushes switch an actual core's short bit on the complete marked board. -/
theorem encodedSegments_core_east_five (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (ha : g.left + 1 < p.axes)
    (hi : g.internal + 1 < state.internal.length)
    (hshort : state.internal.getD (g.internal + 1) false = false)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none
      {player := (coreRail p g.left ha).cell 1,
        boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))ᶜ}
      {player := (coreRail p g.left ha).cell 6,
        boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1)
          (l.encodedSegments p (withShort state g.internal true)))ᶜ} := by
  have h := core_east_five p state kind g.left g.internal ha hi hshort
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateRest l p state g))
    (gate_rest_window_clear l p hl hM haxes state hg hk ha hi) B hB
  rw [gate_full_split l p state hg hk,
    gate_full_split l p (withShort state g.internal true) hg hk, gateRest_set_short l p state hg hk true]
  exact h

/-- The reverse complete-board short-bit switch uses the corresponding five westward pushes. -/
theorem encodedSegments_core_west_five (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) (ha : g.left + 1 < p.axes)
    (hi : g.internal + 1 < state.internal.length)
    (hshort : state.internal.getD (g.internal + 1) false = true)
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    Reachable B none
      {player := (coreRail p g.left ha).cell 9,
        boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))ᶜ}
      {player := (coreRail p g.left ha).cell 4,
        boxes := (SegmentRecipe.holes (p.W + 1) (p.H + 1)
          (l.encodedSegments p (withShort state g.internal false)))ᶜ} := by
  have h := core_west_five p state kind g.left g.internal ha hi hshort
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateRest l p state g))
    (gate_rest_window_clear l p hl hM haxes state hg hk ha hi) B hB
  rw [gate_full_split l p state hg hk,
    gate_full_split l p (withShort state g.internal false) hg hk, gateRest_set_short l p state hg hk false]
  exact h

end PushPuzzle.PushS.PortLayout

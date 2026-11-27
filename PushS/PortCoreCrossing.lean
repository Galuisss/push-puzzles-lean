/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointEnumeration
import all PushS.PortEndpointCrossing
import all PushS.PortEndpointEnumeration
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! Separation of the actual endpoint and three-port core components. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem gate_signal_span (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) :
    p.x (first + 1) - 2 ≤ q.1 ∧ q.1 ≤ p.x (first + 1) + 12 := by
  rw [← List.take_append_drop 2 (gateSegments (coordinates p) state kind first internal),
    pointHoles_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · exact gateSegments_horizontal_span p state kind first internal hq
  · dsimp only [gateSegments] at hq
    simp only [List.drop_succ_cons, List.drop_zero, vertical_mem] at hq
    change q.1 = p.x (first + 1) ∧ _ at hq
    omega

private theorem gate_fixed_span (p : Scales.Parameters) (middle : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle)) :
    p.x middle - 2 ≤ q.1 ∧ q.1 ≤ p.x middle + 12 := by
  change (coordinates p).x middle - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x middle + 12
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs
  · obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hs
    have hv := vertical_coordinates hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · have hp := point_coordinates hq
      omega
    · have hh := horizontal_coordinates hq
      omega
    · have hp := point_coordinates hq
      omega
    · have hp := point_coordinates hq
      omega
  · split at hs
    · obtain ⟨col, hcol, rfl⟩ := List.mem_map.mp hs
      have hp := point_coordinates hq
      simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hcol
      omega
    · cases hs

private theorem gate_signal_page (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) : p.D + 32 < q.2 := by
  have hband := gateSegments_working_band p state kind first internal hq
  have hu := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem lower_segment_page (p : Scales.Parameters) {x u y v : ℕ}
    (hy : y + 32 < p.D) (hv : v + 32 < p.D) {q : ℕ × ℕ}
    (hq : (segment x (onSide (coordinates p) .lower y) u (onSide (coordinates p) .lower v)).Contains q) :
    p.D + 32 < q.2 := by
  simpa using segment_page p .lower hy hv hq

private theorem gate_fixed_page (p : Scales.Parameters) (middle : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle)) : p.D + 32 < q.2 := by
  have hu : (coordinates p).depth 1 + 64 < p.D := readDepth_add_lt_D p 1
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs
  · obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs
    exact lower_segment_page p (by omega) (by omega) hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl <;>
      exact lower_segment_page p (by omega) (by omega) hq
  · split at hs
    · have hn : (coordinates p).depth 2 + 64 < p.D := readDepth_add_lt_D p 2
      obtain ⟨_, _, rfl⟩ := List.mem_map.mp hs
      exact lower_segment_page p (by omega) (by omega) hq
    · cases hs

/-- Endpoint fixed pieces and core signals at distinct axes have disjoint hole unions. -/
private theorem endpointFixedSegments_disjoint_gate_of_port_ne (l : PortLayout)
    (p : Scales.Parameters)
    (state : SignalState) (e : Endpoint) (kind : Shuttle.Kind) (first internal : ℕ)
    (hp : e.port ≠ first + 1) :
    Disjoint (pointHoles (endpointFixedSegments l (coordinates p) e))
      (pointHoles (gateSegments (coordinates p) state kind first internal)) := by
  apply Finset.disjoint_left.mpr
  intro q he hg
  have hE := fixed_endpoint_span l p e he
  have hG := gate_signal_span p state kind first internal hg
  have hm := readDepth_readLength_margin p 0 e.level
  rcases lt_or_gt_of_ne hp with hp | hp
  · have hx := axis_spacing p hp
    omega
  · have hx := axis_spacing p hp
    omega

/-- Core fixed pieces and endpoint signals at distinct axes have disjoint hole unions. -/
private theorem gateFixedSegments_disjoint_endpoint_of_port_ne (p : Scales.Parameters)
    (state : SignalState)
    (middle : ℕ) (e : Endpoint) (hp : middle ≠ e.port) :
    Disjoint (pointHoles (gateFixedSegments (coordinates p) middle))
      (pointHoles (endpointSegments (coordinates p) state e)) := by
  apply Finset.disjoint_left.mpr
  intro q hg he
  have hG := gate_fixed_span p middle hg
  have hE := signal_span p state e he
  rcases lt_or_gt_of_ne hp with hp | hp
  · have hx := axes_separated p hp
    omega
  · have hx := axes_separated p hp
    omega

/-- Every actual core fixed piece is disjoint from every actual core signal piece. -/
private theorem gateFixedSegments_disjoint_gateSegments (p : Scales.Parameters)
    (state : SignalState)
    (first middleFirst : ℕ) (kind : Shuttle.Kind) (internal : ℕ) :
    Disjoint (pointHoles (gateFixedSegments (coordinates p) (first + 1)))
      (pointHoles (gateSegments (coordinates p) state kind middleFirst internal)) := by
  by_cases hp : first = middleFirst
  · subst middleFirst
    exact gateFixedSegments_disjoint p state kind first internal
  · apply Finset.disjoint_left.mpr
    intro q hf hg
    have hF := gate_fixed_span p (first + 1) hf
    have hG := gate_signal_span p state kind middleFirst internal hg
    rcases lt_or_gt_of_ne hp with hp | hp
    · have hx := axes_separated p (show first + 1 < middleFirst + 1 by omega)
      omega
    · have hx := axes_separated p (show middleFirst + 1 < first + 1 by omega)
      omega

private theorem placement_endpoints (l : PortLayout) {g : Placement} (hg : g ∈ placements l) :
    (⟨g.side, g.left, true, g.level, g.internal⟩ : Endpoint) ∈ l.endpoints ∧
      (⟨g.side, g.right, false, g.level,
        g.internal + if g.gate.isSome then 2 else 0⟩ : Endpoint) ∈ l.endpoints :=
  ⟨List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_self⟩,
    List.mem_flatMap.mpr ⟨g, hg, List.mem_cons_of_mem _ List.mem_cons_self⟩⟩

private theorem placement_gate_shape (l : PortLayout) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    g.side = .lower ∧ g.right = g.left + 2 := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · cases hk
  · cases lower with
    | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum] at hk
    | gate kind' first => exact ⟨rfl, rfl⟩

private theorem placement_gate_mem (l : PortLayout) {g : Placement} {kind : Shuttle.Kind}
    (hg : g ∈ placements l) (hk : g.gate = some kind) : .gate kind g.left ∈ l.lowerGroups := by
  simp only [placements, List.mem_append, List.mem_map] at hg
  rcases hg with ⟨⟨⟨a, b⟩, i⟩, hi, rfl⟩ | ⟨⟨lower, i⟩, hi, rfl⟩
  · cases hk
  · cases lower with
    | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum] at hk
    | gate kind' first =>
      simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr, Option.some.injEq] at hk
      subst kind'
      simpa only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr] using
        List.fst_mem_of_mem_zipIdx hi

private theorem center_gate_mem (l : PortLayout) {middle : ℕ} (hm : middle ∈ centers l) :
    ∃ kind first, .gate kind first ∈ l.lowerGroups ∧ middle = first + 1 := by
  obtain ⟨g, hg, hm⟩ := List.mem_filterMap.mp hm
  cases g with
  | wire a b => simp [encLowerGroup_elim, encLowerGroup_toSum] at hm
  | gate kind first =>
    simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr, Option.some.injEq] at hm
    exact ⟨kind, first, hg, hm.symm⟩

/-- An actual endpoint fixed piece is disjoint from every actual lower-gate signal core. -/
theorem endpointFixedSegments_disjoint_actual_gate (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints)
    {kind : Shuttle.Kind} {first : ℕ} (hg : .gate kind first ∈ l.lowerGroups) (internal : ℕ) :
    Disjoint (pointHoles (endpointFixedSegments l (coordinates p) e))
      (pointHoles (gateSegments (coordinates p) state kind first internal)) := by
  by_cases hp : e.port = first + 1
  · cases hs : e.side with
    | upper =>
      apply Finset.disjoint_left.mpr
      intro q hqe hqg
      have hE := fixed_endpoint_page l p e hqe
      have hG := gate_signal_page p state kind first internal hqg
      simp only [hs, ite_true] at hE
      omega
    | lower => exact (l.endpoints_lower_ne_gate_middle hl hg he hs hp).elim
  · exact endpointFixedSegments_disjoint_gate_of_port_ne l p state e kind first internal hp

/-- An actual lower-gate fixed piece is disjoint from every actual endpoint signal. -/
theorem gateFixedSegments_disjoint_actual_endpoint (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {kind : Shuttle.Kind} {first : ℕ}
    (hg : .gate kind first ∈ l.lowerGroups) {e : Endpoint} (he : e ∈ l.endpoints) :
    Disjoint (pointHoles (gateFixedSegments (coordinates p) (first + 1)))
      (pointHoles (endpointSegments (coordinates p) state e)) := by
  by_cases hp : first + 1 = e.port
  · cases hs : e.side with
    | upper =>
      apply Finset.disjoint_left.mpr
      intro q hqg hqe
      have hG := gate_fixed_page p (first + 1) hqg
      have hE := signal_endpoint_page p state e hqe
      simp only [hs, ite_true] at hE
      omega
    | lower => exact (l.endpoints_lower_ne_gate_middle hl hg he hs hp.symm).elim
  · exact gateFixedSegments_disjoint_endpoint_of_port_ne p state (first + 1) e hp

/-- The full actual endpoint-fixed flatMap is disjoint from all emitted physical signals. -/
theorem endpointsFixed_disjoint_signalSegments (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    Disjoint (pointHoles (l.endpoints.flatMap (endpointFixedSegments l (coordinates p))))
      (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hf hs
  obtain ⟨sf, hsf, hqf⟩ := (mem_pointHoles _ q).mp hf
  obtain ⟨e, he, hsf⟩ := List.mem_flatMap.mp hsf
  have hfixed := (mem_pointHoles _ q).mpr ⟨sf, hsf, hqf⟩
  obtain ⟨ss, hss, hqs⟩ := (mem_pointHoles _ q).mp hs
  rcases List.mem_append.mp hss with hss | hss
  · obtain ⟨f, hf, hss⟩ := List.mem_flatMap.mp hss
    exact Finset.disjoint_left.mp (l.endpoints_fixed_disjoint p hl hM state he hf) hfixed
      ((mem_pointHoles _ q).mpr ⟨ss, hss, hqs⟩)
  · obtain ⟨g, hg, hss⟩ := List.mem_flatMap.mp hss
    cases hgate : g.gate with
    | none => simp [tripleSignal, hgate] at hss
    | some kind =>
      have hraw := placement_gate_mem l hg hgate
      have hd := l.endpointFixedSegments_disjoint_actual_gate p hl state he hraw g.internal
      exact Finset.disjoint_left.mp hd hfixed
        ((mem_pointHoles _ q).mpr ⟨ss, by simpa [tripleSignal, hgate] using hss, hqs⟩)

/-- Every actual lower-gate fixed piece is disjoint from the complete emitted signal union. -/
theorem gateFixedSegments_disjoint_signalSegments (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {kind : Shuttle.Kind} {first : ℕ}
    (hg : .gate kind first ∈ l.lowerGroups) :
    Disjoint (pointHoles (gateFixedSegments (coordinates p) (first + 1)))
      (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hsignal
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact Finset.disjoint_left.mp (l.gateFixedSegments_disjoint_actual_endpoint p hl state hg he)
      hfixed ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
  · obtain ⟨g, _, hs⟩ := List.mem_flatMap.mp hs
    cases hgate : g.gate with
    | none => simp [tripleSignal, hgate] at hs
    | some kind =>
      have hd := gateFixedSegments_disjoint_gateSegments p state first g.left kind g.internal
      exact Finset.disjoint_left.mp hd hfixed
        ((mem_pointHoles _ q).mpr ⟨s, by simpa [tripleSignal, hgate] using hs, hq⟩)

end PushPuzzle.PushS.PortLayout

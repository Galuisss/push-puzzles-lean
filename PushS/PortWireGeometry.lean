/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireIndexing
import all PushS.PortWireIndexing
import all PushS.PortAxisClear
import all PushS.PortLayoutCoordinates
import all PushS.PortEndpointCrossing
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortSegmentBounds
import all PushS.PortCentralStrip
import all PushS.PortSegments

/-! Empty working-row intervals of the actual ordinary WIRE groups. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe PageLevels

private theorem next_depth_le (p : Scales.Parameters) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.levels) :
    readDepth p (i + 1) ≤ readDepth p j := by
  rw [readDepth_eq p (by omega) (by omega), readDepth_eq p (by omega) hj]
  exact Y_le p (by omega)

private theorem depth_gap (p : Scales.Parameters) {i j : ℕ}
    (hi : 1 ≤ i) (hij : i < j) (hj : j ≤ p.levels) :
    readDepth p i + 8 < readDepth p j := by
  have hs := readDepth_interlevel_margin p hi (show i < p.levels by omega)
  have hm := next_depth_le p hi hij hj
  omega

private theorem side_segment_before (p : Scales.Parameters) (side : Side) {x u a b y : ℕ}
    (ha : a < y) (hb : b < y) (hy : y ≤ p.H) {q : ℕ × ℕ}
    (hq : (segment x (onSide (coordinates p) side a) u (onSide (coordinates p) side b)).Contains q) :
    q.2 ≠ onSide (coordinates p) side y := by
  intro hrow
  cases side <;> simp [segment, Segment.Contains, onSide, coordinates] at hq hrow <;> omega

private theorem endpoint_fixed_before (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {j : ℕ} (he : 1 ≤ e.level) (hej : e.level < j) (hj : j ≤ p.levels) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    q.2 ≠ onSide (coordinates p) e.side (readDepth p j) := by
  have hg := depth_gap p he hej hj
  have hn := next_depth_le p he hej hj
  have hs := depth_gap p he (show e.level < e.level + 1 by omega) (show e.level + 1 ≤ p.levels by omega)
  have hY := readDepth_add_lt_H p j
  have hcur : (coordinates p).depth e.level + 8 < readDepth p j := hg
  have hnext : (coordinates p).depth (e.level + 1) ≤ readDepth p j := hn
  have hsucc : (coordinates p).depth e.level + 8 < (coordinates p).depth (e.level + 1) := hs
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | hmem | hmem
  · exact side_segment_before p e.side (by omega) (by omega) (by omega) hq
  · exact side_segment_before p e.side (by omega) (by omega) (by omega) hq
  · exact side_segment_before p e.side (by omega) (by omega) (by omega) hq
  · obtain ⟨v, _, hmem⟩ := List.mem_flatMap.mp hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    all_goals split at hmem
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    all_goals subst s
    all_goals exact side_segment_before p e.side (by omega) (by omega) (by omega) hq
  · split at hmem
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      all_goals exact side_segment_before p e.side (by omega) (by omega) (by omega) hq
    · cases hmem

private theorem endpoint_fixed_workrow (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : 1 ≤ e.level) (hm : e.level ≤ p.levels) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e))
    (hy : q.2 = onSide (coordinates p) e.side (readDepth p e.level)) :
    if e.inward then q.1 ≤ p.x e.port else p.x e.port ≤ q.1 := by
  have hY : 16384 ≤ (coordinates p).depth e.level := readDepth_ge p he hm
  have hH : (coordinates p).depth e.level + 64 < p.H := readDepth_add_lt_H p e.level
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  change q.2 = onSide (coordinates p) e.side ((coordinates p).depth e.level) at hy
  change if e.inward then q.1 ≤ (coordinates p).x e.port else (coordinates p).x e.port ≤ q.1
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hmem
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hmem
  rcases hmem with rfl | rfl | rfl | hmem | hmem
  · have hv := vertical_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hv ⊢ <;> omega
  · exact False.elim ((side_segment_before p e.side (by omega) (by omega) (by omega) hq) hy)
  · have hv := horizontal_coordinates hq
    have heq := rows_injective p e.side (by omega) (by omega) (hv.1.symm.trans hy)
    omega
  · obtain ⟨v, _, hmem⟩ := List.mem_flatMap.mp hmem
    rcases List.mem_append.mp hmem with hmem | hmem
    · split at hmem
      · simp only [List.mem_singleton] at hmem
        subst s
        have hp := point_coordinates hq
        cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hp ⊢ <;> omega
      · cases hmem
    · split at hmem
      · simp only [List.mem_singleton] at hmem
        subst s
        exact False.elim ((side_segment_before p e.side (by omega) (by omega) (by omega) hq) hy)
      · cases hmem
  · split at hmem
    · rename_i hj
      change e.level < p.levels at hj
      have hg : (coordinates p).depth e.level + 8 < (coordinates p).depth (e.level + 1) :=
        depth_gap p he (by omega) (by omega)
      have hn : (coordinates p).depth (e.level + 1) + 64 < p.H := readDepth_add_lt_H p (e.level + 1)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      all_goals have hv := point_coordinates hq
      all_goals have heq := rows_injective p e.side (by omega) (by omega) (hv.2.symm.trans hy)
      all_goals omega
    · cases hmem

private theorem span_port_bounds (p : Scales.Parameters) {a b i r x : ℕ}
    (hr : r < p.D) (hx : p.x i - r ≤ x ∧ x ≤ p.x i + r)
    (ha : p.x a < x) (hb : x < p.x b) : a ≤ i ∧ i ≤ b := by
  constructor
  · by_contra! h
    have := axis_spacing p h
    omega
  · by_contra! h
    have := axis_spacing p h
    omega

private theorem row_other_page (p : Scales.Parameters) {side other : Side} (hs : side ≠ other)
    (j : ℕ) {q : ℕ × ℕ}
    (hq : if other = .upper then q.2 + 32 < p.D else p.D + 32 < q.2) :
    q.2 ≠ onSide (coordinates p) side (readDepth p j) := by
  have hy := readDepth_add_lt_D p j
  have hH : p.H = 2 * p.D := rfl
  cases side <;> cases other <;> simp [onSide, coordinates] at hs hq ⊢ <;> omega

private theorem wire_fixed_endpoint_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  by_cases hs : e.side = g.side
  · have hspan := fixed_endpoint_span l p e hq
    have hb := span_port_bounds p (by have := readDepth_readLength_margin p 0 e.level; omega)
      hspan hlo hhi
    obtain ⟨heLo, heHi⟩ := l.endpoints_level_bounds p hl hM he
    obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
    by_cases hleft : e.port = g.left
    · have heq := l.endpoints_key_injective hl he heL hs hleft
      subst e
      have hc := endpoint_fixed_workrow l p (wireLeft g) heLo heHi hq hy
      change q.1 ≤ p.x g.left at hc
      omega
    by_cases hright : e.port = g.right
    · have heq := l.endpoints_key_injective hl he heR hs hright
      subst e
      have hc := endpoint_fixed_workrow l p (wireRight g) heLo heHi hq hy
      change p.x g.right ≤ q.1 at hc
      omega
    have hlevel := interior_endpoint_shallower l hl hg hw he hs (by omega) (by omega)
    have htarget := placement_level_bounds l hl hg
    have hn := endpoint_fixed_before l p e heLo hlevel (by omega) hq
    exact hn (by simpa only [hs] using hy)
  · exact row_other_page p (Ne.symm hs) g.level (fixed_endpoint_page l p e hq) hy

private theorem endpoint_signal_before (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {j : ℕ} (he : 1 ≤ e.level) (hej : e.level < j) (hj : j ≤ p.levels) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) :
    q.2 ≠ onSide (coordinates p) e.side (readDepth p j) := by
  have hg : (coordinates p).depth e.level + 8 < readDepth p j := depth_gap p he hej hj
  have hy := readDepth_add_lt_H p j
  have hbit := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  all_goals exact side_segment_before p e.side (by omega) (by omega) (by omega) hq

private theorem wire_signal_endpoint_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {e : Endpoint} (he : e ∈ l.endpoints)
    (hneL : e ≠ wireLeft g) (hneR : e ≠ wireRight g) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  by_cases hs : e.side = g.side
  · have hspan := signal_span p state e hq
    have hb := span_port_bounds p (by have := readDepth_readLength_margin p 0 0; omega)
      hspan hlo hhi
    obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
    have hleft : e.port ≠ g.left := fun hp => hneL (l.endpoints_key_injective hl he heL hs hp)
    have hright : e.port ≠ g.right := fun hp => hneR (l.endpoints_key_injective hl he heR hs hp)
    have hlevel := interior_endpoint_shallower l hl hg hw he hs (by omega) (by omega)
    obtain ⟨heLo, _⟩ := l.endpoints_level_bounds p hl hM he
    have htarget := placement_level_bounds l hl hg
    have hn := endpoint_signal_before p state e heLo hlevel (by omega) hq
    exact hn (by simpa only [hs] using hy)
  · exact row_other_page p (Ne.symm hs) g.level (signal_endpoint_page p state e hq) hy

private theorem lower_wire_level (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) (hs : g.side = .lower) : 2 ≤ g.level := by
  have ho := wire_owner l hg hw
  rw [hs] at ho
  obtain ⟨i, hi, hlevel⟩ := ho
  have hb := Pages.lowerLevel_wire_ge_two l.pages hl hi
  change 2 ≤ levelFor l .lower i at hb
  rwa [hlevel] at hb

private theorem gate_fixed_before (p : Scales.Parameters) (middle : ℕ) {j : ℕ}
    (hj : 2 ≤ j) (hm : j ≤ p.levels) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle)) :
    q.2 ≠ onSide (coordinates p) .lower (readDepth p j) := by
  have hg : (coordinates p).depth 1 + 8 < readDepth p j := depth_gap p (by omega) (by omega) hm
  have hn : (coordinates p).depth 2 ≤ readDepth p j := next_depth_le p (by omega) (by omega) hm
  have hs : (coordinates p).depth 1 + 8 < (coordinates p).depth 2 :=
    depth_gap p (by omega) (by omega) (by omega)
  have hy := readDepth_add_lt_H p j
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [gateFixedSegments] at hmem
  simp only [List.mem_append, or_assoc] at hmem
  rcases hmem with hmem | hmem | hmem
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hmem
    exact side_segment_before p .lower (by omega) (by omega) (by omega) hq
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    all_goals exact side_segment_before p .lower (by omega) (by omega) (by omega) hq
  · split at hmem
    · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hmem
      exact side_segment_before p .lower (by omega) (by omega) (by omega) hq
    · cases hmem

private theorem wire_fixed_gate_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) (middle : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level)) : False := by
  cases hs : g.side with
  | upper =>
    exact row_other_page p (by decide : Side.upper ≠ .lower) g.level
      (gate_fixed_page p middle hq) (by simpa only [hs] using hy)
  | lower =>
    have hb := placement_level_bounds l hl hg
    exact gate_fixed_before p middle (lower_wire_level l hl hg hw hs) (by omega) hq
      (by simpa only [hs] using hy)

private theorem wire_signal_gate_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) (kind : Shuttle.Kind) (first internal : ℕ)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level)) : False := by
  cases hs : g.side with
  | upper =>
    exact row_other_page p (by decide : Side.upper ≠ .lower) g.level
      (gate_signal_page p state kind first internal hq) (by simpa only [hs] using hy)
  | lower =>
    have hb := placement_level_bounds l hl hg
    have htwo := lower_wire_level l hl hg hw hs
    have hgap := depth_gap p (show 1 ≤ 1 by omega) (show 1 < g.level by omega) (show g.level ≤ p.levels by omega)
    have hband := gateSegments_working_band p state kind first internal hq
    have hH : p.H = 2 * p.D := rfl
    simp only [hs, onSide, reduceCtorEq, ite_false, coordinates] at hy
    have hmargin := readDepth_add_lt_H p g.level
    omega

private theorem placement_wide_clear (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hports : g.left < g.right ∧ g.right < l.portCount) (side : Side)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (wideFixed l (coordinates p) side))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨⟨a, b⟩, hab, hmem⟩ := List.mem_flatMap.mp hmem
  dsimp only at hmem
  split at hmem
  · obtain ⟨v, hv, hmem⟩ := List.mem_filterMap.mp hmem
    split at hmem
    · cases hmem
    · rename_i hnot
      simp only [Option.some.injEq] at hmem
      subst s
      have hp := point_coordinates hq
      have hvH := workingRow_le l p hv
      by_cases hs : side = g.side
      · subst side
        have hY := readDepth_add_lt_H p g.level
        have hrow := rows_injective p g.side (by omega) (by omega) (hp.2.symm.trans hy)
        subst v
        have hgap := adjacentPair_gap hab
        have hb := hports
        have hleft := axis_in_pageColumns l p hl g.side (lt_trans hb.1 hb.2)
        have hright := axis_in_pageColumns l p hl g.side hb.2
        have hnoL := hgap.2 _ hleft
        have hnoR := hgap.2 _ hright
        have ha : p.x g.left ≤ a := by omega
        have hb : b ≤ p.x g.right := by omega
        have hcross : crosses l (coordinates p) g.side a b (readDepth p g.level) = true := by
          apply List.any_eq_true.mpr
          refine ⟨g, hg, ?_⟩
          exact decide_eq_true ⟨rfl, rfl, ha, hgap.1, hb⟩
        exact hnot hcross
      · have hvY := workingRows_le_last l p hv
        have hlast := last_depth_margin p
        have hband := segment_page p side (by omega) (by omega) hq
        exact row_other_page p (Ne.symm hs) g.level hband hy
  · cases hmem

private theorem wire_wide_clear (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) (side : Side)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (wideFixed l (coordinates p) side))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False :=
  placement_wide_clear l p hl hg (wire_ports l hl hg hw) side hq hy hlo hhi

end PushPuzzle.PushS.PortLayout

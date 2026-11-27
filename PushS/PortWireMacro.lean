/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireClear
import all PushS.PortWireClear
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortAxisMacro
import all PushS.PortSegments

/-! Full marked-board horizontal pushes for the actual upper and lower ordinary WIREs. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def onWire (g : Placement) (e : Endpoint) : Bool :=
  decide (e.side = g.side ∧ (e.port = g.left ∨ e.port = g.right))

private def wireRest (l : PortLayout) (p : Scales.Parameters) (state : SignalState) (g : Placement) :
    List Segment :=
  l.fixedSegments p ++
    ((l.endpoints.filter fun e => !(onWire g e)).flatMap (endpointSegments (coordinates p) state) ++
      (placements l).flatMap (tripleSignal (coordinates p) state))

private theorem filtered_other (l : PortLayout) (g : Placement) {e : Endpoint}
    (he : e ∈ l.endpoints.filter fun e => !(onWire g e)) :
    e ∈ l.endpoints ∧ e ≠ wireLeft g ∧ e ≠ wireRight g := by
  have hf := List.mem_filter.mp he
  refine ⟨hf.1, ?_, ?_⟩
  · intro h; subst e; simp [onWire, wireLeft] at hf
  · intro h; subst e; simp [onWire, wireRight] at hf

private theorem onWire_owner (l : PortLayout) (hl : l.pages.Valid) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {e : Endpoint} (he : e ∈ l.endpoints)
    (h : onWire g e = true) : e = wireLeft g ∨ e = wireRight g := by
  obtain ⟨hside, hport⟩ := of_decide_eq_true h
  obtain ⟨heL, heR⟩ := wire_endpoints l hg hw
  exact hport.elim (fun h => Or.inl (l.endpoints_key_injective hl he heL hside h))
    (fun h => Or.inr (l.endpoints_key_injective hl he heR hside h))

private theorem wire_rest_set (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) (gain : Bool) :
    wireRest l p {state with internal := state.internal.set g.internal gain} g =
      wireRest l p state g := by
  unfold wireRest
  congr 2
  · apply List.flatMap_congr
    intro e he
    obtain ⟨he, hneL, hneR⟩ := filtered_other l g he
    have hn := wire_endpoint_internal l hg hw he hneL hneR
    simp only [endpointSegments, List.getD, List.getElem?_set_ne hn.symm]
  · apply List.flatMap_congr
    intro h hh
    cases hc : h.gate with
    | none => simp only [tripleSignal, hc, Option.elim]
    | some kind =>
      have h0 := wire_core_internal l hg hw hh hc (j := 0) (by omega)
      have h1 := wire_core_internal l hg hw hh hc (j := 1) (by omega)
      have h2 := wire_core_internal l hg hw hh hc (j := 2) (by omega)
      simp only [Nat.add_zero] at h0
      simp only [tripleSignal, hc, Option.elim, gateSegments, List.getD,
        List.getElem?_set_ne h0.symm, List.getElem?_set_ne h1.symm, List.getElem?_set_ne h2.symm]
      rfl

private theorem wire_endpoints_split (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state)) =
      pointHoles ((l.endpoints.filter fun e => !(onWire g e)).flatMap (endpointSegments (coordinates p) state)) ∪
        (pointHoles (endpointSegments (coordinates p) state (wireLeft g)) ∪
          pointHoles (endpointSegments (coordinates p) state (wireRight g))) := by
  ext q
  simp only [Finset.mem_union]
  constructor
  · intro hq
    obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    cases h : onWire g e with
    | false => exact Or.inl ((mem_pointHoles _ q).mpr
        ⟨s, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [h]⟩, hs⟩, hq⟩)
    | true =>
      rcases onWire_owner l hl hg hw he h with rfl | rfl
      · exact Or.inr (Or.inl ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩))
      · exact Or.inr (Or.inr ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩))
  · intro hq
    have lift (e : Endpoint) (he : e ∈ l.endpoints) (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) :
        q ∈ pointHoles (l.endpoints.flatMap (endpointSegments (coordinates p) state)) := by
      obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
      exact (mem_pointHoles _ q).mpr ⟨s, List.mem_flatMap.mpr ⟨e, he, hs⟩, hq⟩
    rcases hq with hq | hq | hq
    · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
      obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
      exact lift e (List.mem_filter.mp he).1 ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
    · exact lift _ (wire_endpoints l hg hw).1 hq
    · exact lift _ (wire_endpoints l hg hw).2 hq

private theorem wire_full_split (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireRest l p state g) ∪
      SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (endpointSegments (coordinates p) state (wireLeft g) ++
          endpointSegments (coordinates p) state (wireRight g)) := by
  ext q
  simp only [Finset.mem_union, finite_mem, encodedSegments, signalSegments, rawSignals,
    wireRest, pointHoles_append, Finset.mem_union]
  rw [wire_endpoints_split l p hl state hg hw, Finset.mem_union, Finset.mem_union]
  tauto

private theorem wire_rest_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (wireRest l p state g))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False := by
  simp only [wireRest, pointHoles_append, Finset.mem_union] at hq
  rcases hq with hfixed | hend | hcore
  · exact wire_fixed_clear l p hl hM ha hg hw hfixed hy hlo hhi
  · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hend
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨he, hneL, hneR⟩ := filtered_other l g he
    exact wire_signal_endpoint_clear l p hl hM state hg hw he hneL hneR
      ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hy (by omega) (by omega)
  · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hcore
    obtain ⟨h, _, hs⟩ := List.mem_flatMap.mp hs
    cases hc : h.gate with
    | none => simp only [tripleSignal, hc, Option.elim, List.not_mem_nil] at hs
    | some kind =>
      exact wire_signal_gate_clear l p hl hM state hg hw kind h.left h.internal
        ((mem_pointHoles _ q).mpr ⟨s, by simpa only [tripleSignal, hc, Option.elim] using hs, hq⟩) hy

private theorem full_wire_step (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hindex : g.internal < state.internal.length) (gain : Bool)
    (hbefore : state.internal.getD g.internal false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x g.left + 1 else p.x g.right - 1,
        onSide (coordinates p) g.side (readDepth p g.level)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set g.internal gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x g.left + 2 else p.x g.right - 2,
          onSide (coordinates p) g.side (readDepth p g.level)) := by
  let ambient := SegmentRecipe.holes (p.W + 1) (p.H + 1) (wireRest l p state g)
  have hb := wire_ports l hl hg hw
  have hgap := axis_spacing p hb.1
  have hD := readDepth_readLength_margin p 0 0
  have hfree : Disjoint ambient (SegmentRecipe.holes (p.W + 1) (p.H + 1)
      [⟨(p.x g.left + 2, onSide (coordinates p) g.side (readDepth p g.level)),
        (p.x g.right - 2, onSide (coordinates p) g.side (readDepth p g.level))⟩]) := by
    apply Finset.disjoint_left.mpr
    intro q hqA hq
    rw [SegmentRecipe.mem_holes] at hq
    obtain ⟨seg, hs, hq⟩ := hq
    simp only [List.mem_singleton] at hs
    subst seg
    have hh : q.2.val = onSide (coordinates p) g.side (readDepth p g.level) ∧
        p.x g.left + 2 ≤ q.1.val ∧ q.1.val ≤ p.x g.right - 2 := by
      dsimp only [Segment.Contains] at hq
      omega
    exact wire_rest_clear l p hl hM ha state hg hw ((finite_mem p _ q).mp hqA) hh.1 hh.2.1 hh.2.2
  obtain ⟨t, hstep, ht, hplayer⟩ := wire_step p state (wireLeft g) (wireRight g)
    rfl rfl rfl rfl rfl hb.1 (lt_of_lt_of_le hb.2 ha) hindex gain hbefore ambient hfree s
    (hempty.trans (wire_full_split l p hl state hg hw)) hp B hB
  refine ⟨t, hstep, ?_, hplayer⟩
  rw [wire_full_split l p hl _ hg hw, wire_rest_set l p state hg hw gain]
  exact ht

section Source

variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)

include hl hM ha

/-- One actual upper-page pair performs its internal-bit flip on the complete marked board. -/
theorem encodedSegments_upper_wire_step (i : Fin l.upperPairs.length)
    (hindex : i.val < state.internal.length) (gain : Bool)
    (hbefore : state.internal.getD i.val false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x (l.upperPairs.get i).1 + 1 else p.x (l.upperPairs.get i).2 - 1,
        readDepth p (l.upperLevel i)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set i.val gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x (l.upperPairs.get i).1 + 2 else p.x (l.upperPairs.get i).2 - 2,
          readDepth p (l.upperLevel i)) := by
  let g : Placement := ⟨.upper, (l.upperPairs.get i).1, (l.upperPairs.get i).2,
    l.upperLevel i, i.val, none⟩
  have hg : g ∈ placements l := by
    apply List.mem_append_left
    refine List.mem_map.mpr ⟨(l.upperPairs.get i, i.val), ?_, rfl⟩
    simp only [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem i.isLt]
    rfl
  exact full_wire_step l p hl hM ha state hg rfl hindex gain hbefore s hempty hp B hB

/-- One actual lower WIRE group performs its internal-bit flip on the complete marked board. -/
theorem encodedSegments_lower_wire_step (i : Fin l.lowerGroups.length) (a b : ℕ)
    (hgroup : l.lowerGroups.get i = .wire a b)
    (hindex : l.lowerOffset i < state.internal.length) (gain : Bool)
    (hbefore : state.internal.getD (l.lowerOffset i) false = !gain)
    (s : HoleState (p.W + 1) (p.H + 1))
    (hempty : s.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hp : (s.player.1.val, s.player.2.val) =
      (if gain then p.x a + 1 else p.x b - 1, p.H - readDepth p (l.lowerLevel i)))
    (B : Board (p.W + 1) (p.H + 1)) (hB : B.walls = ∅) :
    ∃ t : HoleState (p.W + 1) (p.H + 1), Step B none s.toState t.toState ∧
      t.empty = SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.encodedSegments p {state with internal := state.internal.set (l.lowerOffset i) gain}) ∧
      (t.player.1.val, t.player.2.val) =
        (if gain then p.x a + 2 else p.x b - 2, p.H - readDepth p (l.lowerLevel i)) := by
  let g : Placement := ⟨.lower, a, b, l.lowerLevel i, l.lowerOffset i, none⟩
  have hg : g ∈ placements l := by
    apply List.mem_append_right
    refine List.mem_map.mpr ⟨(.wire a b, i.val), ?_, ?_⟩
    · simp only [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem i.isLt]
      exact congrArg some hgroup
    · simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inl]
      rfl
  exact full_wire_step l p hl hM ha state hg rfl hindex gain hbefore s hempty hp B hB

end Source

end PushPuzzle.PushS.PortLayout

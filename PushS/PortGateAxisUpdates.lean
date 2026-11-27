/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateAxis
public import PushS.PortGateUpdates
import all PushS.PortGateAxis
import all PushS.PortGateUpdates
import all PushS.PortAxisMacro
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! A middle-axis bit update preserves every actual hole outside its four-hole open segment. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem endpoint_axes_off_gateAxis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (gain : Bool) {e : Endpoint} (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hout : q ∉ gateAxis p (g.left + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (endpointSegments (coordinates p) {state with axes := state.axes.set (g.left + 1) gain} e) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e) := by
  by_cases hport : e.port = g.left + 1
  · have heq := upper_gate_axis_owner l hl hg hk hu hsu hp he hport
    subst e
    have hnot (s : SignalState) : q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1)
        ((endpointSegments (coordinates p) s upper).take 1) := by
      intro hq
      apply hout
      apply gate_axis_near_inside l p hl hM s kind g.left g.internal upper hu hsu hp
      exact (finite_append p _ _ q).mpr (Or.inl hq)
    rw [finite_take_drop p (endpointSegments (coordinates p)
        {state with axes := state.axes.set (g.left + 1) gain} upper) 1,
      finite_take_drop p (endpointSegments (coordinates p) state upper) 1]
    simp only [hnot, false_or]
    have hhor : (endpointSegments (coordinates p)
        {state with axes := state.axes.set (g.left + 1) gain} upper).drop 1 =
        (endpointSegments (coordinates p) state upper).drop 1 := by
      simp only [endpointSegments, List.drop_succ_cons, List.drop_zero]
    rw [hhor]
  · rw [endpoint_set_other p state e (g.left + 1) gain hport]

private theorem core_axes_off_gateAxis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (gain : Bool) {h : Placement} (hh : h ∈ placements l) {q : Cell (p.W + 1) (p.H + 1)}
    (hout : q ∉ gateAxis p (g.left + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (tripleSignal (coordinates p) {state with axes := state.axes.set (g.left + 1) gain} h) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (tripleSignal (coordinates p) state h) := by
  by_cases hmid : h.left + 1 = g.left + 1
  · cases hhk : h.gate with
    | none => simp only [tripleSignal, hhk, Option.elim_none]
    | some other =>
      have heq := same_gate_middle l hl hg hh hk hhk hmid
      subst h
      simp only [tripleSignal, hk, Option.elim_some]
      have hnot (s : SignalState) : q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1)
          ((gateSegments (coordinates p) s kind g.left g.internal).drop 2) := by
        intro hq
        apply hout
        apply gate_axis_near_inside l p hl hM s kind g.left g.internal upper hu hsu hp
        exact (finite_append p _ _ q).mpr (Or.inr hq)
      rw [finite_take_drop p (gateSegments (coordinates p)
          {state with axes := state.axes.set (g.left + 1) gain} kind g.left g.internal) 2,
        finite_take_drop p (gateSegments (coordinates p) state kind g.left g.internal) 2]
      simp only [hnot, or_false]
      have hhor : (gateSegments (coordinates p)
          {state with axes := state.axes.set (g.left + 1) gain} kind g.left g.internal).take 2 =
          (gateSegments (coordinates p) state kind g.left g.internal).take 2 := by
        simp only [gateSegments, List.take_succ_cons, List.take_zero]
      rw [hhor]
  · rw [core_set_other p state h (g.left + 1) gain hmid]

/-- Flipping an actual middle-axis bit preserves every complete-board hole outside its open axis. -/
theorem encodedSegments_gate_axes_offAxis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (gain : Bool) {q : Cell (p.W + 1) (p.H + 1)} (hout : q ∉ gateAxis p (g.left + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with axes := state.axes.set (g.left + 1) gain}) ↔
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  simp only [encodedSegments, signalSegments, rawSignals, finite_append, finite_flatMap]
  apply or_congr Iff.rfl
  apply or_congr
  · constructor
    · rintro ⟨e, he, hq⟩
      exact ⟨e, he, (endpoint_axes_off_gateAxis l p hl hM state hg hk hu hsu hp gain he hout).mp hq⟩
    · rintro ⟨e, he, hq⟩
      exact ⟨e, he, (endpoint_axes_off_gateAxis l p hl hM state hg hk hu hsu hp gain he hout).mpr hq⟩
  · constructor
    · rintro ⟨h, hh, hq⟩
      exact ⟨h, hh, (core_axes_off_gateAxis l p hl hM state hg hk hu hsu hp gain hh hout).mp hq⟩
    · rintro ⟨h, hh, hq⟩
      exact ⟨h, hh, (core_axes_off_gateAxis l p hl hM state hg hk hu hsu hp gain hh hout).mpr hq⟩

private theorem gate_axis_segments_mem (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind) (upper : Endpoint) (hsu : upper.side = .upper)
    (hp : upper.port = g.left + 1) (q : Cell (p.W + 1) (p.H + 1))
    (hx : q.1.val = p.x (g.left + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateAxisSegments p state kind g.left g.internal upper) ↔
      (readDepth p upper.level ≤ q.2.val ∧ q.2.val ≤ readDepth p upper.level + 1 + (state.axes.getD (g.left + 1) false).toNat) ∨
      (p.H - (readDepth p 1 + 2 - (state.axes.getD (g.left + 1) false).toNat) ≤ q.2.val ∧
        q.2.val ≤ p.H - (readDepth p 1 + 1)) := by
  rw [gateAxisSegments, finite_append]
  simp only [finite_point_mem, axis_mem]
  simp only [gateSegments, List.drop_succ_cons, List.drop_zero, vertical_mem, hsu, hp, onSide,
    ite_true, reduceCtorEq, ite_false]
  have hb := Bool.toNat_le (state.axes.getD (g.left + 1) false)
  have hH := readDepth_add_lt_H p 1
  change ((q.1.val = _ ∧ _ ≤ q.2.val ∧ q.2.val ≤ _) ∨ (q.1.val = _ ∧ _ ≤ q.2.val ∧ q.2.val ≤ _)) ↔ _
  have hcx : (coordinates p).x (g.left + 1) = p.x (g.left + 1) := rfl
  have hcy : (coordinates p).depth 1 = readDepth p 1 := rfl
  have hheight : (coordinates p).H = p.H := rfl
  rw [hcx, hcy, hheight]
  omega

/-- The full actual middle-axis open segment has exactly its two canonical near-axis intervals. -/
theorem encodedSegments_gateAxis_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateAxis p (g.left + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      (readDepth p upper.level ≤ q.2.val ∧ q.2.val ≤ readDepth p upper.level + 1 + (state.axes.getD (g.left + 1) false).toNat) ∨
      (p.H - (readDepth p 1 + 2 - (state.axes.getD (g.left + 1) false).toNat) ≤ q.2.val ∧
        q.2.val ≤ p.H - (readDepth p 1 + 1)) := by
  have heq := l.encodedSegments_gateAxis p hl hM ha state hg hk hu hsu hp
  have hmem : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateAxisSegments p state kind g.left g.internal upper) := by
    rw [← heq]
    simp only [Finset.mem_inter, hq, and_true]
  exact hmem.trans (gate_axis_segments_mem p state g kind upper hsu hp q (Finset.mem_filter.mp hq).2.1)

private structure GateAxisGeometry (p : Scales.Parameters) (upper : Endpoint) : Prop where
  upperPositive : 16384 ≤ readDepth p upper.level
  upperCut : readDepth p upper.level + 64 < p.D
  lowerPositive : 16384 ≤ readDepth p 1
  lowerCut : readDepth p 1 + 64 < p.D
  height : p.H = 2 * p.D

private theorem gate_axis_geometry (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {upper : Endpoint} (hu : upper ∈ l.endpoints) :
    GateAxisGeometry p upper :=
  ⟨readDepth_ge p (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2,
    readDepth_add_lt_D p upper.level, readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos,
    readDepth_add_lt_D p 1, rfl⟩

private theorem gate_axis_transfer_inside (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement} {upper : Endpoint}
    (hu : upper ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x (g.left + 1))
    (hy : q.2.val = readDepth p upper.level + 2 ∨ q.2.val = p.H - (readDepth p 1 + 2)) :
    q ∈ gateAxis p (g.left + 1) := by
  obtain ⟨hup, huc, hlp, hlc, hH⟩ := gate_axis_geometry l p hl hM hu
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, by omega, by omega⟩

private theorem gate_axis_update (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (state : SignalState)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    (gain : Bool) (hi : g.left + 1 < state.axes.length)
    (hbefore : state.axes.getD (g.left + 1) false = !gain) (q z : Cell (p.W + 1) (p.H + 1))
    (hqx : q.1.val = p.x (g.left + 1)) (hzx : z.1.val = p.x (g.left + 1))
    (hqy : q.2.val = if gain then readDepth p upper.level + 2 else p.H - (readDepth p 1 + 2))
    (hzy : z.2.val = if gain then p.H - (readDepth p 1 + 2) else readDepth p upper.level + 2) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.encodedSegments p {state with axes := state.axes.set (g.left + 1) gain}) =
      insert q ((SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)).erase z) := by
  have hqR := gate_axis_transfer_inside l p hl hM hu (g := g) hqx (by cases gain <;> simp_all)
  have hzR := gate_axis_transfer_inside l p hl hM hu (g := g) hzx (by cases gain <;> simp_all)
  ext r
  by_cases hr : r ∈ gateAxis p (g.left + 1)
  · have hrx := (Finset.mem_filter.mp hr).2.1
    have hqpoint : r = q ↔ r.2.val = (if gain then readDepth p upper.level + 2 else p.H - (readDepth p 1 + 2)) := by
      simp only [Prod.ext_iff, Fin.ext_iff, hqx, hqy, hrx, true_and]
    have hzpoint : r = z ↔ r.2.val = (if gain then p.H - (readDepth p 1 + 2) else readDepth p upper.level + 2) := by
      simp only [Prod.ext_iff, Fin.ext_iff, hzx, hzy, hrx, true_and]
    rw [l.encodedSegments_gateAxis_mem p hl hM ha
      {state with axes := state.axes.set (g.left + 1) gain} hg hk hu hsu hp hr,
      Finset.mem_insert, Finset.mem_erase, hqpoint]
    simp only [ne_eq, hzpoint]
    rw [l.encodedSegments_gateAxis_mem p hl hM ha state hg hk hu hsu hp hr]
    have hset : (state.axes.set (g.left + 1) gain).getD (g.left + 1) false = gain := List.getD_set_self hi
    obtain ⟨hup, huc, hlp, hlc, hH⟩ := gate_axis_geometry l p hl hM hu
    cases gain <;> simp only [Bool.not_false, Bool.not_true] at hbefore <;>
      simp only [hset, hbefore, Bool.false_eq_true, ite_false, ite_true, Bool.toNat_false, Bool.toNat_true] <;> omega
  · have hqne : r ≠ q := fun h => hr (h ▸ hqR)
    have hzne : r ≠ z := fun h => hr (h ▸ hzR)
    rw [Finset.mem_insert, Finset.mem_erase]
    simp only [hqne, false_or]
    have hoff := l.encodedSegments_gate_axes_offAxis p hl hM state hg hk hu hsu hp gain hr
    exact ⟨fun h => ⟨hzne, hoff.mp h⟩, fun h => hoff.mpr h.2⟩

end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisFixed
public import PushS.PortOrdinaryAxis
public import PushS.PortGateShuttle
import all PushS.PortOrdinaryAxis
import all PushS.PortGateShuttle
import all PushS.PortGateIndexing
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortCoreCounts
import all PushS.PortEndpointCounts
import all PushS.PortSegmentInventory
import all PushS.PortAxisClear
import all PushS.PortSegments

/-! Four canonical holes on the actual middle axis above a three-port work row. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The gate's middle axis above its lower work row, excluding the upper frame cell. -/
@[expose] def gateAxis (p : Scales.Parameters) (middle : ℕ) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.1.val = p.x middle ∧ 0 < q.2.val ∧ q.2.val < p.H - readDepth p 1

/-- The upper endpoint and lower core's actual axis-near traces. -/
def gateAxisSegments (p : Scales.Parameters) (state : SignalState) (kind : Shuttle.Kind)
    (first internal : ℕ) (upper : Endpoint) : List Segment :=
  (endpointSegments (coordinates p) state upper).take 1 ++
    (gateSegments (coordinates p) state kind first internal).drop 2

private theorem same_gate_middle (l : PortLayout) (hl : l.pages.Valid) {g h : Placement}
    (hg : g ∈ placements l) (hh : h ∈ placements l) {kind other : Shuttle.Kind}
    (hk : g.gate = some kind) (hhk : h.gate = some other) (hmid : h.left + 1 = g.left + 1) : h = g := by
  have hside := (placement_gate_shape l hh hhk).1.trans (placement_gate_shape l hg hk).1.symm
  have heq := l.endpoints_key_injective hl (placement_endpoints l hh).1 (placement_endpoints l hg).1 hside
    (by change h.left = g.left; omega)
  have hi : h.internal = g.internal := congrArg Endpoint.internal heq
  exact first_slot_owner l hh hg (by omega) (by simp only [slotCount, hhk, Option.isSome_some, ite_true]; omega)

private theorem upper_gate_axis_owner (l : PortLayout) (hl : l.pages.Valid)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {e : Endpoint} (he : e ∈ l.endpoints) (hport : e.port = g.left + 1) : e = upper := by
  have hside : e.side = .upper := by
    cases hs : e.side with
    | upper => rfl
    | lower => exact False.elim (l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he hs hport)
  exact l.endpoints_key_injective hl he hu (hside.trans hsu.symm) (hport.trans hp.symm)

private theorem endpoint_on_gate_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1)
    {e : Endpoint} (he : e ∈ l.endpoints) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) (hx : q.1 = p.x (g.left + 1)) :
    q ∈ pointHoles ((endpointSegments (coordinates p) state upper).take 1) := by
  by_cases hport : e.port = g.left + 1
  · have heq := upper_gate_axis_owner l hl hg hk hu hsu hp he hport
    subst e
    rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state upper), pointHoles_append,
      Finset.mem_union] at hq
    exact hq.resolve_right (fun h => horizontal_near_off_axis p state upper h (by simpa only [hp] using hx))
  · have hspan := signal_span p state e hq
    exact False.elim (off_axis_of_span p hport (r := 2)
      (by have := readDepth_readLength_margin p 0 0; omega) hspan hx)

private theorem core_on_gate_axis (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {h : Placement} (hh : h ∈ placements l) {other : Shuttle.Kind} (hhk : h.gate = some other)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (gateSegments (coordinates p) state other h.left h.internal))
    (hx : q.1 = p.x (g.left + 1)) (hy : q.2 < p.H - readDepth p 1) :
    q ∈ pointHoles ((gateSegments (coordinates p) state kind g.left g.internal).drop 2) := by
  have hspan := gate_signal_span p state other h.left h.internal hq
  have hmid : h.left + 1 = g.left + 1 := by
    by_contra hn
    exact off_axis_of_span p hn (r := 12) (by have := readDepth_readLength_margin p 0 0; omega) (by omega) hx
  have heq := same_gate_middle l hl hg hh hk hhk hmid
  subst h
  have hkind : other = kind := Option.some.inj (hhk.symm.trans hk)
  subst other
  rw [← List.take_append_drop 2 (gateSegments (coordinates p) state kind g.left g.internal),
    pointHoles_append, Finset.mem_union] at hq
  refine hq.resolve_left ?_
  intro hhoriz
  dsimp only [gateSegments] at hhoriz
  simp only [List.take_succ_cons, List.take_zero, mem_pointHoles, List.mem_cons, List.not_mem_nil,
    or_false, exists_eq_or_imp, exists_eq_left] at hhoriz
  rcases hhoriz with hhoriz | hhoriz
  all_goals have hr := (horizontal_coordinates hhoriz).1
  all_goals change q.2 = p.H - readDepth p 1 at hr
  all_goals omega

private theorem gate_axis_near_inside (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (upper : Endpoint) (hu : upper ∈ l.endpoints)
    (hsu : upper.side = .upper) (hp : upper.port = first + 1) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateAxisSegments p state kind first internal upper)) :
    q ∈ gateAxis p (first + 1) := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases List.mem_append.mp hs with hs | hs
  · have hh := (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩
    have hi := (Finset.mem_filter.mp (axis_near_inside l p hl hM state upper hu hh)).2
    have hy := upper_axis_row p state upper hsu ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    exact ⟨by simpa only [hp] using hi.1, hi.2.1, by omega⟩
  · have hq : (q.1.val, q.2.val) ∈ pointHoles ((gateSegments (coordinates p) state kind first internal).drop 2) :=
      (mem_pointHoles _ _).mpr ⟨s, hs, hc⟩
    have hY := readDepth_add_lt_H p 1
    have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
    dsimp only [gateSegments] at hq
    simp only [List.drop_succ_cons, List.drop_zero, vertical_mem] at hq
    change q.1.val = p.x (first + 1) ∧
      min (p.H - (readDepth p 1 + 1)) (p.H - (readDepth p 1 + 2 - (state.axes.getD (first + 1) false).toNat)) ≤ q.2.val ∧
      q.2.val ≤ max (p.H - (readDepth p 1 + 1)) (p.H - (readDepth p 1 + 2 - (state.axes.getD (first + 1) false).toNat)) at hq
    exact ⟨hq.1, by omega, by omega⟩

/-- The complete board has exactly the two emitted axis traces above an actual gate's work row. -/
theorem encodedSegments_gateAxis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ gateAxis p (g.left + 1) =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateAxisSegments p state kind g.left g.internal upper) := by
  ext q
  constructor
  · intro hq
    obtain ⟨hh, hr⟩ := Finset.mem_inter.mp hq
    have hr := (Finset.mem_filter.mp hr).2
    apply (finite_mem p _ q).mpr
    rw [gateAxisSegments, pointHoles_append]
    have hh := (finite_mem p _ q).mp hh
    simp only [encodedSegments, signalSegments, rawSignals, pointHoles_append, Finset.mem_union] at hh
    rcases hh with hfixed | hend | hcore
    · have hsource := l.fixedSegments_on_main_axis p hl hM ha
        (gate_middle_lt l hl (placement_gate_mem l hg hk)) hfixed hr.1
      have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
      have hH := readDepth_add_lt_H p 1
      rcases hsource with hz | hH | ⟨_, hy⟩ <;> omega
    · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hend
      obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
      exact Finset.mem_union_left _ (endpoint_on_gate_axis l p hl state hg hk hu hsu hp he
        ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hr.1)
    · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hcore
      obtain ⟨h, hh, hs⟩ := List.mem_flatMap.mp hs
      cases hhk : h.gate with
      | none => simp only [tripleSignal, hhk, Option.elim_none, List.not_mem_nil] at hs
      | some other =>
        exact Finset.mem_union_right _ (core_on_gate_axis l p hl state hg hk hh hhk
          ((mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hhk, Option.elim_some] using hs, hc⟩) hr.1 hr.2.2)
  · intro hq
    have haxis := gate_axis_near_inside l p hl hM state kind g.left g.internal upper hu hsu hp hq
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    have hsig : (q.1.val, q.2.val) ∈ pointHoles (l.signalSegments p state) := by
      rcases List.mem_append.mp hs with hs | hs
      · exact (mem_pointHoles _ _).mpr ⟨s, List.mem_append_left _
          (List.mem_flatMap.mpr ⟨upper, hu, List.mem_of_mem_take hs⟩), hc⟩
      · exact core_signal_mem l p state hg hk ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_drop hs, hc⟩)
    refine Finset.mem_inter.mpr ⟨?_, haxis⟩
    apply (finite_mem p _ q).mpr
    rw [encodedSegments, pointHoles_append]
    exact Finset.mem_union_right _ hsig

/-- Every canonical assignment has four holes on the actual gate middle-axis open segment. -/
theorem encodedSegments_gateAxis_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ gateAxis p (g.left + 1)).card = 4 := by
  rw [l.encodedSegments_gateAxis p hl hM ha state hg hk hu hsu hp, SegmentRecipe.holes_card_of_bounds]
  · exact gateMiddleAxis_card p state kind g.left g.internal upper hsu hp
      (l.endpoints_level_bounds p hl hM hu).1 (l.endpoints_level_bounds p hl hM hu).2
  · intro q hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    have hsig : q ∈ pointHoles (l.signalSegments p state) := by
      rcases List.mem_append.mp hs with hs | hs
      · exact (mem_pointHoles _ _).mpr ⟨s, List.mem_append_left _
          (List.mem_flatMap.mpr ⟨upper, hu, List.mem_of_mem_take hs⟩), hc⟩
      · exact core_signal_mem l p state hg hk ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_drop hs, hc⟩)
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hsig
    have hb := l.signalSegments_contains_bounds p hl ha state hs hc
    omega

end PushPuzzle.PushS.PortLayout

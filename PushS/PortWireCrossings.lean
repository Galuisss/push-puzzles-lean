/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortColumnRadius
public import PushS.PortWireMacro
import all PushS.PortWireMacro
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates

/-! Actual ordinary WIRE interiors and their crossings with endpoint and gate columns. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The complete marked board has no initial hole in the interior of an ordinary WIRE,
beyond its two short receiving slots. -/
theorem wireInterior_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (hlo : p.x g.left + 3 ≤ q.1.val) (hhi : q.1.val ≤ p.x g.right - 3) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [wire_full_split l p hl state hg hw]
  intro hq
  rcases Finset.mem_union.mp hq with hrest | hpair
  · obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hrest
    exact wire_rest_clear l p hl hM ha state hg hw ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hy
      (by omega) (by omega)
  · obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hpair
    rcases List.mem_append.mp hs with hs | hs
    · have hspan := (endpoint_near p state (wireLeft g) ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)).1
      change p.x g.left ≤ q.1.val ∧ q.1.val ≤ p.x g.left + 2 at hspan
      omega
    · have hspan := (endpoint_near p state (wireRight g) ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)).1
      change p.x g.right - 2 ≤ q.1.val ∧ q.1.val ≤ p.x g.right at hspan
      have hx := readLength_add_lt_x p g.right 0
      omega

/-- Every actual ordinary WIRE interior cell starts occupied. -/
theorem physicalInstance_wireInterior_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    (hlo : p.x g.left + 3 ≤ q.1.val) (hhi : q.1.val ≤ p.x g.right - 3) :
    q ∈ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  by_contra hbox
  have hh := (mem_holes _).mpr hbox
  rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
  change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) at hh
  exact l.wireInterior_not_hole p hl hM ha initial hg hw hy hlo hhi hh

private theorem crossing_band (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {e : Endpoint} (he : e ∈ l.endpoints) (hside : e.side = g.side)
    (hleft : g.left < e.port) (hright : e.port < g.right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 12)
    (hy : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level) :
    q ∈ axisDeepBand p e.side e.port e.level := by
  have hlevel := interior_endpoint_shallower l hl hg hw he hside hleft hright
  have helevel := l.endpoints_level_bounds p hl hM he
  have hglevel := placement_level_bounds l hl hg
  have hnext := next_depth_le p helevel.1 hlevel (show g.level ≤ p.levels by omega)
  have hgap := readDepth_interlevel_margin p helevel.1 (show e.level < p.levels by omega)
  have hmax := readDepth_le_last p g.level
  have hy' : q.2.val = if e.side = .upper then readDepth p g.level else p.H - readDepth p g.level := by
    simpa only [hside] using hy
  refine ⟨hx, ?_⟩
  cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy' ⊢ <;> omega

private theorem interior_column_bounds (p : Scales.Parameters) {left middle right : ℕ}
    (hleft : left < middle) (hright : middle < right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12) :
    p.x left + 3 ≤ q.1.val ∧ q.1.val ≤ p.x right - 3 := by
  have hleftgap := axis_spacing p hleft
  have hrightgap := axis_spacing p hright
  have hd := p.outer_distance
  simp only [Nat.dist] at hx
  constructor <;> omega

private theorem gate_crossing_band (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) (hside : g.side = .lower)
    {middle : ℕ} {q : Cell (p.W + 1) (p.H + 1)}
    (hx : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12)
    (hy : q.2.val = p.H - readDepth p g.level) :
    1 < p.levels ∧ q ∈ axisDeepBand p .lower middle 1 := by
  obtain ⟨i, hi, hgi⟩ : ∃ i : l.pages.lowerPage.Index,
      l.pages.lowerPage.group i = .wire g.left g.right ∧ l.pages.lowerLevel i = g.level := by
    have ho := wire_owner l hg hw
    rw [hside] at ho
    exact ho
  have htwo := l.pages.lowerLevel_wire_ge_two hl hi
  have hglevel := placement_level_bounds l hl hg
  have hgM : g.level ≤ p.levels := by omega
  have hn := next_depth_le p (show 1 ≤ 1 by omega) (show 1 < g.level by omega) hgM
  have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) (show 1 < p.levels by omega)
  have hmax := readDepth_le_last p g.level
  refine ⟨by omega, hx, ?_⟩
  change p.H - (p.Y p.levels + 2) ≤ q.2.val ∧
    q.2.val ≤ p.H - (readDepth p 1 + readDepth p (1 + 1)) / 2
  omega

/-- Crossings of an actual ordinary WIRE with a shallower endpoint's column remain occupied
and are never reached by the player in a successful physical play. -/
theorem physicalInstance_wire_crossing (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    {e : Endpoint} (he : e ∈ l.endpoints) (hside : e.side = g.side)
    (hleft : g.left < e.port) (hright : e.port < g.right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 12)
    (hy : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  have hlevel := interior_endpoint_shallower l hl hg hw he hside hleft hright
  have hglevel := placement_level_bounds l hl hg
  have heM : e.level < p.levels := by omega
  have hband := crossing_band l p hl hM hg hw he hside hleft hright hx hy
  obtain ⟨hlo, hhi⟩ := interior_column_bounds p hleft hright hx
  exact ⟨l.physicalInstance_endpoint_deep_unvisited p hl hM ha initial target e he heM hband hsu hut ht,
    l.physicalInstance_endpoint_deep_occupied p hl hM ha initial target e he heM hband
      (l.physicalInstance_wireInterior_initial_full p hl hM ha initial target hg hw hy hlo hhi) hsu hut ht⟩

/-- Crossings of an actual lower WIRE with a three-port middle column stay occupied
and cannot be visited during a successful physical play. -/
theorem physicalInstance_wire_gate_crossing (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none)
    (hside : g.side = .lower) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (hleft : g.left < middle) (hright : middle < g.right)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 12)
    (hy : q.2.val = p.H - readDepth p g.level)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    u.player ≠ q ∧ q ∈ u.boxes := by
  obtain ⟨hlevels, hband⟩ := gate_crossing_band l p hl hM hg hw hside hx hy
  obtain ⟨hlo, hhi⟩ := interior_column_bounds p hleft hright hx
  have hy' : q.2.val = if g.side = .upper then readDepth p g.level else p.H - readDepth p g.level := by
    simpa only [hside, reduceCtorEq, ite_false] using hy
  exact ⟨l.physicalInstance_gate_deep_unvisited p hl hM ha initial target hi hlevels hband hsu hut ht,
    l.physicalInstance_gate_deep_occupied p hl hM ha initial target hi hlevels hband
      (l.physicalInstance_wireInterior_initial_full p hl hM ha initial target hg hw hy' hlo hhi) hsu hut ht⟩

end PushPuzzle.PushS.PortLayout

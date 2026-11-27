/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateIndexing
public import PushS.PortGatePageWindow
public import PushS.PortWireClear
import all PushS.PortGateIndexing
import all PushS.PortGatePageWindow
import all PushS.PortWireClear
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortCoreCrossing
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegmentBounds
import all PushS.PortSegments
import all PushS.PortSegmentInventory
import all PushS.ShuttleMacroSegments

/-! Complete-board source classification of the actual three-port horizontal open rail. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The first lower work row strictly between a three-port group's outer axes. -/
@[expose] def gateOpenRail (p : Scales.Parameters) (g : Placement) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Finset.univ.filter fun q => q.2.val = p.H - readDepth p 1 ∧
    p.x g.left < q.1.val ∧ q.1.val < p.x g.right

/-- The actual two outer receiving slots and the core's G/J gaps, in emitter order. -/
def gateHorizontalSegments (p : Scales.Parameters) (state : SignalState) (g : Placement)
    (kind : Shuttle.Kind) : List Segment :=
  (endpointSegments (coordinates p) state (gateLeft g)).drop 1 ++
    (endpointSegments (coordinates p) state (gateRight g)).drop 1 ++
      (gateSegments (coordinates p) state kind g.left g.internal).take 2

private theorem gate_workrow (l : PortLayout) (p : Scales.Parameters) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    onSide (coordinates p) g.side (readDepth p g.level) = p.H - readDepth p 1 := by
  simp only [(placement_gate_shape l hg hk).1, gate_level_one l hg hk, onSide,
    reduceCtorEq, ite_false, coordinates]

private theorem gate_endpoint_between (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind}
    (hk : g.gate = some kind) {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower)
    {r x : ℕ} (hr : r < p.D) (hspan : p.x e.port - r ≤ x ∧ x ≤ p.x e.port + r)
    (hlo : p.x g.left < x) (hhi : x < p.x g.right) : e = gateLeft g ∨ e = gateRight g := by
  have hb := span_port_bounds p hr hspan hlo hhi
  have hshape := placement_gate_shape l hg hk
  have hgends := gate_endpoints l hg hk
  by_cases hleft : e.port = g.left
  · exact Or.inl (l.endpoints_key_injective hl he hgends.1 (hs.trans hshape.1.symm) hleft)
  by_cases hright : e.port = g.right
  · exact Or.inr (l.endpoints_key_injective hl he hgends.2 (hs.trans hshape.1.symm) hright)
  have hmiddle : e.port = g.left + 1 := by omega
  exact False.elim (l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he hs hmiddle)

private theorem workrow_source_lower (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) {q : ℕ × ℕ} (hy : q.2 = p.H - readDepth p 1)
    (hsource : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e) ∨
      q ∈ pointHoles (endpointSegments (coordinates p) state e)) : e.side = .lower := by
  have hp := hsource.elim (fixed_endpoint_page l p e) (signal_endpoint_page p state e)
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hp ⊢
  omega

private theorem gate_fixed_endpoint_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {e : Endpoint} (he : e ∈ l.endpoints) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e))
    (hy : q.2 = p.H - readDepth p 1) (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  have hs := workrow_source_lower l p ⟨[], []⟩ e hy (Or.inl hq)
  have hspan := fixed_endpoint_span l p e hq
  have helevel := l.endpoints_level_bounds p hl hM he
  have hrow : q.2 = onSide (coordinates p) g.side (readDepth p g.level) :=
    hy.trans (gate_workrow l p hg hk).symm
  rcases gate_endpoint_between l p hl hg hk he hs
      (by have := readDepth_readLength_margin p 0 e.level; omega) hspan hlo hhi with rfl | rfl
  · have hh := endpoint_fixed_workrow l p (gateLeft g) helevel.1 helevel.2 hq hrow
    change q.1 ≤ p.x g.left at hh
    omega
  · have hh := endpoint_fixed_workrow l p (gateRight g) helevel.1 helevel.2 hq hrow
    change p.x g.right ≤ q.1 at hh
    omega

private theorem gate_fixed_workrow_clear (p : Scales.Parameters) (middle : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) middle))
    (hy : q.2 = p.H - readDepth p 1) : False := by
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hH := readDepth_add_lt_H p 1
  cases gateFixedSegments_location p middle hq with
  | publicStreet _ hdepth => omega
  | privateCap _ hrow => omega
  | privateBranch hrow _ => omega
  | halfDepth hrow => omega
  | marker hlevels _ hrow =>
    have hg := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
    change 2 * p.b 1 + 6 < (readDepth p 2 - readDepth p 1) / 2 - 2 at hg
    have hn := readDepth_add_lt_H p 2
    omega

private theorem interior_gate_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (interiorFixed l (coordinates p)))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  have hy' := hy.trans (gate_workrow l p hg hk)
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact gate_fixed_endpoint_clear l p hl hM hg hk he ((mem_pointHoles _ q).mpr ⟨s, hs, hc⟩) hy' hlo hhi
  · obtain ⟨middle, _, hs⟩ := List.mem_flatMap.mp hs
    exact gate_fixed_workrow_clear p middle ((mem_pointHoles _ q).mpr ⟨s, hs, hc⟩) hy'
  · exact placement_wide_clear l p hl hg (gate_port_bounds l hl hg hk) .upper
      ((mem_pointHoles _ q).mpr ⟨s, hs, hc⟩) hy hlo hhi
  · exact placement_wide_clear l p hl hg (gate_port_bounds l hl hg hk) .lower
      ((mem_pointHoles _ q).mpr ⟨s, hs, hc⟩) hy hlo hhi
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := point_coordinates hc
    have hgap := working_row_gap p g.side g.level
    simp only [coordinates] at hp
    omega

/-- The complete marked fixed-hole background avoids the active three-port horizontal interior. -/
theorem gateFixed_workrow_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (l.fixedSegments p))
    (hy : q.2 = p.H - readDepth p 1) (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False :=
  fixed_workrow_clear l p hM ha g (gate_port_bounds l hl hg hk) (placement_level_bounds l hl hg)
    (fun _ h hy hlo hhi => interior_gate_clear l p hl hM hg hk h hy hlo hhi) hq
    (hy.trans (gate_workrow l p hg hk).symm) hlo hhi

private theorem gate_between_owner (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {g h : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    (hh : h ∈ placements l) {other : Shuttle.Kind} (hhk : h.gate = some other) {x : ℕ}
    (hspan : p.x (h.left + 1) - 12 ≤ x ∧ x ≤ p.x (h.left + 1) + 12)
    (hlo : p.x g.left < x) (hhi : x < p.x g.right) : h = g := by
  have hb := span_port_bounds p (by have := readDepth_readLength_margin p 0 0; omega) hspan hlo hhi
  have hshape := placement_gate_shape l hg hk
  have hends := gate_endpoints l hg hk
  have hraw := placement_gate_mem l hh hhk
  have hs := hshape.1
  by_cases hleft : h.left + 1 = g.left
  · exact False.elim (l.endpoints_lower_ne_gate_middle hl hraw hends.1 hs (by
      change g.left = h.left + 1
      omega))
  by_cases hright : h.left + 1 = g.right
  · exact False.elim (l.endpoints_lower_ne_gate_middle hl hraw hends.2 hs (by
      change g.right = h.left + 1
      omega))
  have hport : h.left = g.left := by omega
  have heq := l.endpoints_key_injective hl (gate_endpoints l hh hhk).1 hends.1
    ((placement_gate_shape l hh hhk).1.trans hs.symm) hport
  have hindex : h.internal = g.internal := congrArg Endpoint.internal heq
  exact first_slot_owner l hh hg (by omega) (by
    simp only [slotCount, hhk, Option.isSome_some, ite_true]
    omega)

private theorem endpoint_horizontal_mem (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (q : ℕ × ℕ) : q ∈ pointHoles ((endpointSegments (coordinates p) state e).drop 1) ↔
    q.2 = onSide (coordinates p) e.side (readDepth p e.level) ∧
      (if e.inward then p.x e.port + 1 ≤ q.1 ∧ q.1 ≤ p.x e.port + 1 + (state.internal.getD e.internal false).toNat
      else p.x e.port - (1 + (!(state.internal.getD e.internal false)).toNat) ≤ q.1 ∧ q.1 ≤ p.x e.port - 1) := by
  have hx := readLength_add_lt_x p e.port 0
  have hb := Bool.toNat_le (state.internal.getD e.internal false)
  have hn := Bool.toNat_le (!(state.internal.getD e.internal false))
  dsimp only [endpointSegments]
  simp only [List.drop_succ_cons, List.drop_zero, horizontal_mem]
  have hc : (coordinates p).x e.port = p.x e.port := rfl
  have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
  rw [hc, hd]
  cases e.inward <;> simp only [inward, Bool.false_eq_true, ite_false, ite_true] <;> omega

private theorem endpoint_horizontal_of_off_axis (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e))
    (hx : q.1.val ≠ p.x e.port) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state e).drop 1) := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact False.elim (hx (vertical_coordinates hc).1)
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨_, by simp [endpointSegments], hc⟩

private theorem core_horizontal_of_workrow (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (g : Placement) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateSegments (coordinates p) state kind g.left g.internal))
    (hy : q.2.val = p.H - readDepth p 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((gateSegments (coordinates p) state kind g.left g.internal).take 2) := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  simp only [gateSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨_, by simp [gateSegments], hc⟩
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨_, by simp [gateSegments], hc⟩
  · have hloc := (vertical_coordinates hc).2
    have hb := Bool.toNat_le (state.axes.getD (g.left + 1) false)
    have hH := readDepth_add_lt_H p 1
    have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
    simp only [onSide, reduceCtorEq, ite_false, hd, show (coordinates p).H = p.H from rfl] at hloc
    omega

private theorem finite_point_mem (p : Scales.Parameters) (ss : List Segment)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ss ↔ (q.1.val, q.2.val) ∈ pointHoles ss := by
  simp only [SegmentRecipe.mem_holes, mem_pointHoles]

private theorem horizontal_piece_mem (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) ↔
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state (gateLeft g)).drop 1) ∨
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((endpointSegments (coordinates p) state (gateRight g)).drop 1) ∨
      q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) ((gateSegments (coordinates p) state kind g.left g.internal).take 2) := by
  simp only [gateHorizontalSegments, finite_point_mem, pointHoles_append, Finset.mem_union, or_assoc]

private theorem gate_horizontal_row (p : Scales.Parameters) (state : SignalState)
    (g : Placement) (kind : Shuttle.Kind) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((gateSegments (coordinates p) state kind g.left g.internal).take 2)) :
    q.2 = p.H - readDepth p 1 := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
  simp only [gateSegments, List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  all_goals exact (horizontal_coordinates hc).1

private theorem gateHorizontalSegments_subset_rail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) ⊆ gateOpenRail p g := by
  have hports := gate_port_bounds l hl hg hk
  have hshape := placement_gate_shape l hg hk
  have hgap := axis_spacing p hports.1
  have hleftgap := axis_spacing p (show g.left < g.left + 1 by omega)
  have hrightgap := axis_spacing p (show g.left + 1 < g.right by omega)
  have hD := p.outer_distance
  intro q hq
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases (horizontal_piece_mem p state g kind q).mp hq with hleft | hright | hcore
  · have hslot := (endpoint_horizontal_mem p state (gateLeft g) _).mp ((finite_point_mem p _ q).mp hleft)
    have hy := hslot.1.trans (gate_workrow l p hg hk)
    have hh := hslot.2
    change p.x g.left + 1 ≤ q.1.val ∧ q.1.val ≤ p.x g.left + 1 + (state.internal.getD g.internal false).toNat at hh
    have hb := Bool.toNat_le (state.internal.getD g.internal false)
    exact ⟨hy, by omega, by omega⟩
  · have hslot := (endpoint_horizontal_mem p state (gateRight g) _).mp ((finite_point_mem p _ q).mp hright)
    have hy := hslot.1.trans (gate_workrow l p hg hk)
    have hh := hslot.2
    change p.x g.right - (1 + (!(state.internal.getD (g.internal + 2) false)).toNat) ≤ q.1.val ∧ q.1.val ≤ p.x g.right - 1 at hh
    have hb := Bool.toNat_le (!(state.internal.getD (g.internal + 2) false))
    have hx := readLength_add_lt_x p g.right 0
    exact ⟨hy, by omega, by omega⟩
  · have hcore := (finite_point_mem p _ q).mp hcore
    have hx := gateSegments_horizontal_span p state kind g.left g.internal hcore
    exact ⟨gate_horizontal_row p state g kind hcore, by omega, by omega⟩

private theorem gateHorizontalSegments_mem_signal (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {s : Segment}
    (hs : s ∈ gateHorizontalSegments p state g kind) : s ∈ l.signalSegments p state := by
  obtain ⟨hleft, hright⟩ := gate_endpoints l hg hk
  rcases List.mem_append.mp hs with hs | hs
  · rcases List.mem_append.mp hs with hs | hs
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨gateLeft g, hleft, List.mem_of_mem_drop hs⟩)
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨gateRight g, hright, List.mem_of_mem_drop hs⟩)
  · apply List.mem_append_right
    exact List.mem_flatMap.mpr ⟨g, hg, by
      simpa only [tripleSignal, hk, Option.elim_some] using List.mem_of_mem_take hs⟩

private theorem gate_horizontal_boundary_mem (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind}
    (hk : g.gate = some kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val = p.H - readDepth p 1)
    (hx : q.1.val = p.x g.left + 1 ∨ q.1.val = p.x g.right - 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) := by
  have hrow := gate_workrow l p hg hk
  apply (horizontal_piece_mem p state g kind q).mpr
  rcases hx with hx | hx
  · left
    apply (finite_point_mem p _ q).mpr
    apply (endpoint_horizontal_mem p state (gateLeft g) _).mpr
    exact ⟨hy.trans hrow.symm, by
      change p.x g.left + 1 ≤ q.1.val ∧ q.1.val ≤ p.x g.left + 1 + (state.internal.getD g.internal false).toNat
      omega⟩
  · right; left
    apply (finite_point_mem p _ q).mpr
    apply (endpoint_horizontal_mem p state (gateRight g) _).mpr
    exact ⟨hy.trans hrow.symm, by
      change p.x g.right - (1 + (!(state.internal.getD (g.internal + 2) false)).toNat) ≤ q.1.val ∧ q.1.val ≤ p.x g.right - 1
      omega⟩

private theorem encoded_gate_rail_source (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hr : q ∈ gateOpenRail p g) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) := by
  obtain ⟨hy, hlo, hhi⟩ := (Finset.mem_filter.mp hr).2
  by_cases hboundary : q.1.val = p.x g.left + 1 ∨ q.1.val = p.x g.right - 1
  · exact gate_horizontal_boundary_mem l p state hg hk hy hboundary
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hfixed | hsignal
  · exact False.elim (l.gateFixed_workrow_clear p hl hM ha hg hk
      ((mem_pointHoles _ _).mpr ⟨s, hfixed, hc⟩) hy (by omega) (by omega))
  apply (horizontal_piece_mem p state g kind q).mpr
  rcases List.mem_append.mp hsignal with hend | hcore
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hend
    have hpoint := (mem_pointHoles _ _).mpr ⟨s, hs, hc⟩
    have hsLower := workrow_source_lower l p state e hy (Or.inr hpoint)
    have hspan := signal_span p state e hpoint
    have hpart := (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩
    rcases gate_endpoint_between l p hl hg hk he hsLower
        (by have := readDepth_readLength_margin p 0 0; omega) hspan hlo hhi with rfl | rfl
    · left
      exact endpoint_horizontal_of_off_axis p state (gateLeft g) hpart (by change _ ≠ p.x g.left; omega)
    · right; left
      exact endpoint_horizontal_of_off_axis p state (gateRight g) hpart (by change _ ≠ p.x g.right; omega)
  · obtain ⟨h, hh, hs⟩ := List.mem_flatMap.mp hcore
    cases hhk : h.gate with
    | none => simp only [tripleSignal, hhk, Option.elim_none, List.not_mem_nil] at hs
    | some other =>
      have hspan := gate_signal_span p state other h.left h.internal
        ((mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hhk, Option.elim_some] using hs, hc⟩)
      have heq := gate_between_owner l p hl hg hk hh hhk (by constructor <;> omega) hlo hhi
      subst h
      have hkind : other = kind := Option.some.inj (hhk.symm.trans hk)
      subst other
      right; right
      apply core_horizontal_of_workrow p state kind g ?_ hy
      exact (SegmentRecipe.mem_holes _ q).mpr
        ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩

/-- The actual three-port horizontal rail contains precisely its two receiving slots and G/J. -/
theorem encodedSegments_gateOpenRail (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ gateOpenRail p g =
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateHorizontalSegments p state g kind) := by
  ext q
  constructor
  · intro hq
    exact encoded_gate_rail_source l p hl hM ha state hg hk (Finset.mem_inter.mp hq).1 (Finset.mem_inter.mp hq).2
  · intro hq
    apply Finset.mem_inter.mpr
    refine ⟨?_, gateHorizontalSegments_subset_rail l p hl state hg hk hq⟩
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
    exact (SegmentRecipe.mem_holes _ q).mpr
      ⟨s, List.mem_append_right _ (gateHorizontalSegments_mem_signal l p state hg hk hs), hc⟩

/-- Every canonical physical assignment gives exactly κ+11 holes on the actual open gate rail. -/
theorem encodedSegments_gateOpenRail_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) ∩ gateOpenRail p g).card =
      kind.kappa.toNat + 11 := by
  rw [l.encodedSegments_gateOpenRail p hl hM ha state hg hk, SegmentRecipe.holes_card_of_bounds]
  · have hs := placement_gate_shape l hg hk
    simpa only [gateHorizontalSegments, gateLeft, gateRight, hs.1, hs.2, gate_level_one l hg hk] using
      gateHorizontals_card p state kind g.left g.internal
  · intro q hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    have hb := l.signalSegments_contains_bounds p hl ha state
      (gateHorizontalSegments_mem_signal l p state hg hk hs) hc
    omega

/-- The actual initial open gate rail has its prescribed horizontal hole inventory. -/
theorem physicalInstance_gateOpenRail_initial_holes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (holes (l.physicalInstance p hl hM ha initial target).initial ∩ gateOpenRail p g).card =
      kind.kappa.toNat + 11 := by
  rw [l.physicalInstance_initial_holes p hl hM ha initial target]
  exact l.encodedSegments_gateOpenRail_card p hl hM ha initial hg hk

/-- The exact complete-board storage target has the same open gate rail inventory. -/
theorem physicalInstance_gateOpenRail_target_holes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    (holes t ∩ gateOpenRail p g).card = kind.kappa.toNat + 11 := by
  have hh : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
    change (t.boxes : Finset (Cell (p.W + 1) (p.H + 1)))ᶜ = _
    rw [ht]
    exact l.physicalInstance_goal_holes p hl hM ha initial target
  rw [hh]
  exact l.encodedSegments_gateOpenRail_card p hl hM ha target hg hk

end PushPuzzle.PushS.PortLayout

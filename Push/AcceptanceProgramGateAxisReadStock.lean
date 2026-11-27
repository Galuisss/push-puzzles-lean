/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramGateAxisReadStockPrefix
import all Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramLayout
import all PushS.PortGateAxis
import all PushS.PortCoreCounts
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! The actual combined axis block pays exactly the lower core's canonical near-axis inventory. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- The actual emitted vertical near trace of a lower gate core. -/
@[expose] def gateAxisNearStock (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (g : Placement) (kind : Shuttle.Kind) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  SegmentRecipe.holes (p.W + 1) (p.H + 1)
    ((gateSegments (coordinates p) (l.canonical target) kind g.left g.internal).drop 2)

private theorem gate_near_coordinates (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (g : Placement) (kind : Shuttle.Kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ gateAxisNearStock l p target g kind) :
    q.1.val = p.x (g.left + 1) ∧
      p.H - (p.Y 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - (p.Y 1 + 1) := by
  have hp := (finite_mem p _ q).mp hq
  simp only [gateSegments, List.drop_succ_cons, List.drop_zero, vertical_mem] at hp
  have hY := readDepth_add_lt_H p 1
  have hb := Bool.toNat_le ((l.canonical target).axes.getD (g.left + 1) false)
  change q.1.val = p.x (g.left + 1) ∧
    min (p.H - (readDepth p 1 + 1))
      (p.H - (readDepth p 1 + 2 - ((l.canonical target).axes.getD (g.left + 1) false).toNat)) ≤ q.2.val ∧
    q.2.val ≤ max (p.H - (readDepth p 1 + 1))
      (p.H - (readDepth p 1 + 2 - ((l.canonical target).axes.getD (g.left + 1) false).toNat)) at hp
  rw [readDepth_eq p le_rfl p.levels_pos] at hp hY
  exact ⟨hp.1, by omega, by omega⟩

private theorem gate_near_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateAxisNearStock l p target g kind) :
    q ∈ targetHoles l p target := by
  have hp := (finite_mem p _ q).mp hq
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hp
  have hsig := core_signal_mem l p (l.canonical target) hg hk
    ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_drop hs, hc⟩)
  apply (finite_mem p _ q).mpr
  rw [encodedSegments, pointHoles_append]
  exact Finset.mem_union_right _ hsig

/-- Precisely the lower core near trace remains above the actual R15 core cutoff. -/
private theorem gate_axisRead_before_front_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    ((emit (axisReadBefore l p target) (targetHoles l p target)).remaining.filter
      fun q => q.1.val = p.x (g.left + 1) ∧ q.2.val < p.H - p.Y 1) = gateAxisNearStock l p target g kind := by
  ext q
  constructor
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    obtain ⟨ht, hf⟩ := Finset.mem_sdiff.mp (take_stock_interior l p target 15 (by omega) hq)
    have hq0 : q.2.val ≠ 0 := by
      intro he
      exact hf ((Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩⟩)
    have hR : q ∈ gateAxis p (g.left + 1) := by
      apply Finset.mem_filter.mpr
      rw [readDepth_eq p le_rfl p.levels_pos]
      exact ⟨Finset.mem_univ _, hx, by omega, hy⟩
    have hnear := (congrArg (fun E : Finset (Cell (p.W + 1) (p.H + 1)) => q ∈ E)
      (l.encodedSegments_gateAxis p hl hM haxes (l.canonical target) hg hk hu hsu hp)).mp
        (Finset.mem_inter.mpr ⟨ht, hR⟩)
    obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hnear
    rcases List.mem_append.mp hs with hs | hs
    · have haxis := (axis_mem p (l.canonical target) upper _).mp ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
      rw [readDepth_eq p hj hjm] at haxis
      simp only [hsu, onSide, ite_true] at haxis
      have hnU := emit_stage_excluded (mainRound_mem_axisReadBefore l p target .upper) hq
      have huDepth : p.Y upper.level + 2 ≤ q.2.val := by
        by_contra hn
        apply hnU
        rw [← hsu]
        apply (mainRound_column_region l p hl upper hu (by simpa only [hp] using hx)).mpr
        simpa only [pageDepth, hsu, ite_true] using Nat.lt_of_not_ge hn
      have hb := Bool.toNat_le ((l.canonical target).axes.getD upper.port false)
      have hprobe : q.2.val ∈ probeRows l p := by
        apply List.mem_toFinset.mpr
        exact List.mem_map.mpr ⟨upper, List.mem_filter.mpr ⟨hu, by simp [hsu]⟩, by omega⟩
      exact False.elim (emit_stage_excluded (probe_mem_axisReadBefore l p target) hq
        ((readRows_region p .west _ (Or.inl rfl) q).mpr hprobe))
    · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩
  · intro hq
    obtain ⟨hx, hy⟩ := gate_near_coordinates l p target g kind hq
    have hY := readDepth_add_lt_H p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hY
    exact Finset.mem_filter.mpr ⟨gate_axis_near_before l p hl hM haxes target hg hk hx hy
      (gate_near_target l p target hg hk hq), hx, by omega⟩

/-- The canonical lower core near trace contains two holes minus its target bit. -/
private theorem gateAxisNearStock_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (haxes : l.portCount ≤ p.axes) (target : List Bool)
    {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind) :
    (gateAxisNearStock l p target g kind).card = 2 - (target.getD (g.left + 1) false).toNat := by
  have hcard := gateSegments_axis_card p (l.canonical target) kind g.left g.internal
  rw [gateAxisNearStock, SegmentRecipe.holes_card_of_bounds]
  · change (pointHoles _).card = 2 - ((l.canonical target).axes.getD (g.left + 1) false).toNat
    omega
  · intro q hq
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    have hsig := core_signal_mem l p (l.canonical target) hg hk
      ((mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_drop hs, hc⟩)
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hsig
    have hb := l.signalSegments_contains_bounds p hl haxes (l.canonical target) hs hc
    omega

private theorem gate_axisRead_region (l : PortLayout) (p : Scales.Parameters)
    {middle : ℕ} (hm : middle ∈ l.gateCenterCoordinates)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = p.x middle) :
    q ∈ (axisReadRound l p).region ↔ q.2.val < p.H - p.Y 1 := by
  have hcore : p.x middle ∈ cores l p := gate_core_column l p hm
  constructor
  · intro hr
    obtain ⟨⟨lane, span⟩, hreq, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hr
    change q.1.val = lane at hcol
    rcases List.mem_append.mp hreq with hreq | hreq
    · have hn := ((mem_prefixRequests _ _ lane span).mp hreq).1
      exact False.elim ((Finset.mem_sdiff.mp hn).2 ((hcol.symm.trans hx).symm ▸ hcore))
    · have hn := ((mem_prefixRequests _ _ lane span).mp hreq).2
      simpa only [prefixRank, Direction.position, hn] using hpos
  · intro hy
    apply (mem_readRegion _ _ q).mpr
    exact ⟨(p.x middle, p.H - p.Y 1), List.mem_append_right _
      ((mem_prefixRequests _ _ _ _).mpr ⟨hcore, rfl⟩), hx, hy⟩

/-- The actual combined R15 core read consumes exactly two minus the target axis bit. -/
theorem gate_axisRead_target_column_loss (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l) {kind : Shuttle.Kind} (hk : g.gate = some kind)
    {upper : Endpoint} (hu : upper ∈ l.endpoints) (hsu : upper.side = .upper) (hp : upper.port = g.left + 1) :
    let T := (emit (axisReadBefore l p target) (targetHoles l p target)).remaining
    let U := (emit [axisReadRound l p] T).remaining
    (U.filter fun q => q.1.val = p.x (g.left + 1)).card +
      (2 - (target.getD (g.left + 1) false).toNat) =
        (T.filter fun q => q.1.val = p.x (g.left + 1)).card := by
  classical
  dsimp only
  let T := (emit (axisReadBefore l p target) (targetHoles l p target)).remaining
  let C := T.filter fun q => q.1.val = p.x (g.left + 1)
  let R := gateAxisNearStock l p target g kind
  have hR : R = C.filter (fun q => q ∈ (axisReadRound l p).region) := by
    dsimp only [R]
    rw [← gate_axisRead_before_front_eq l p hl hM haxes target hg hk hu hsu hp]
    ext q
    simp only [C, T, Finset.mem_filter]
    constructor
    · rintro ⟨ht, hx, hy⟩
      exact ⟨⟨ht, hx⟩, (gate_axisRead_region l p (center_of_gate l (placement_gate_mem l hg hk)) q hx).mpr hy⟩
    · rintro ⟨⟨ht, hx⟩, hr⟩
      exact ⟨ht, hx, (gate_axisRead_region l p (center_of_gate l (placement_gate_mem l hg hk)) q hx).mp hr⟩
  have hU : ((emit [axisReadRound l p] T).remaining.filter
      fun q => q.1.val = p.x (g.left + 1)) = C \ R := by
    rw [hR]
    ext q
    simp only [emit_remaining, allRegions, Finset.union_empty, Finset.mem_filter,
      Finset.mem_sdiff, C]
    tauto
  rw [hU, ← gateAxisNearStock_card l p hl haxes target hg hk]
  change (C \ R).card + R.card = C.card
  exact Finset.card_sdiff_add_card_eq_card (by rw [hR]; exact Finset.filter_subset _ _)

end PushPuzzle.Push.AcceptanceProgram

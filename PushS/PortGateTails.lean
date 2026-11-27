/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateMarkers
public import PushS.PortEndpointTail
import all PushS.PortGateMarkers
import all PushS.PortGatePageWindow
import all PushS.PortEndpointRWall
import all PushS.PortCentralFreeze
import all PushS.PortStreetSeparation
import all PushS.PortStreetSupport
import all PushS.PortPageBackground
import all PushS.PortBackground
import all PushS.PortSegments

/-! Full special-column tails between a three-port work band and its actual interlevel holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The actual first interlevel marker depth. -/
@[expose] def gateMarkerDepth (p : Scales.Parameters) : ℕ := (readDepth p 1 + readDepth p 2) / 2

/-- All five special-column tails, from depth `Y₁+3` to their emitted marker holes. -/
noncomputable def gateTails (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => 1 < p.levels ∧ ∃ middle ∈ l.gateCenterCoordinates,
    q.1.val ∈ gateSpecialColumns p middle ∧ ∃ v, readDepth p 1 + 3 ≤ v ∧
      v < gateMarkerDepth p ∧ q.2.val = p.H - v

private theorem gate_tail_data (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateTails p) :
    1 < p.levels ∧ ∃ middle ∈ l.gateCenterCoordinates,
      q.1.val ∈ gateSpecialColumns p middle ∧ ∃ v, readDepth p 1 + 3 ≤ v ∧
        v < gateMarkerDepth p ∧ q.2.val = p.H - v := by
  classical
  simpa only [gateTails, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem tail_source_clear (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle v : ℕ} (hv : readDepth p 1 + 3 ≤ v) (hvm : v < gateMarkerDepth p)
    {q : ℕ × ℕ} (hy : q.2 = p.H - v) (hs : GateHoleSource l p state middle q) : False := by
  have hm := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  dsimp only [gateMarkerDepth] at hvm
  cases hs with
  | fixed hfixed =>
    cases gateFixedSegments_location p middle hfixed with
    | publicStreet _ hr => omega
    | privateCap _ hr => omega
    | privateBranch hr _ => omega
    | halfDepth hr => omega
    | marker _ _ hr => omega
  | @signal kind first internal _ _ hsignal =>
    cases gateSegments_location p state kind first internal hsignal with
    | horizontal hr => omega
    | axis _ hr => omega

/-- The full actual initial encoding occupies every cell of the five gate-column tails. -/
theorem gateTails_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    l.gateTails p ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨_, middle, hi, hx, v, hv, hvm, hy⟩ := gate_tail_data l p hq
  have hs := gate_special_span p hx
  have hm := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hwindow : q ∈ gatePageWindow p middle := by
    dsimp only [gateMarkerDepth] at hvm
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    simp only [Nat.dist]
    omega
  by_contra hbox
  have hh := (mem_holes _).mpr hbox
  rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
  exact tail_source_clear l p initial hv hvm hy
    (l.encodedSegments_gatePageWindow p hl hM ha initial hi hwindow hh)

private theorem tail_not_row (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateTails p) : q.2 ∉ l.workingRowSet p := by
  obtain ⟨hlevels, _, _, _, v, hv, hvm, hy⟩ := gate_tail_data l p hq
  have hm := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  dsimp only [gateMarkerDepth] at hvm
  intro hr
  rcases (l.workingRowSet_iff p q.2).mp hr with h0 | hH' | ⟨w, hw, hrow⟩
  · omega
  · omega
  · have hwmax := workingRows_le_last l p hw
    have hwgap := l.workingDepthCoordinates_interlevel_gap p (show 1 ≤ 1 by omega) hlevels hw
    simp only [Nat.reduceAdd] at hwgap hgap
    rcases hrow with hrow | hrow <;> omega

private theorem gate_west_background (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hpos : 0 < q.1.val) (heven : q.1.val % 2 = 0)
    (hrow : q.2 ∉ l.workingRowSet p) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  let r : Cell (p.W + 1) (p.H + 1) := (⟨q.1.val - 1, by have := q.1.isLt; omega⟩, q.2)
  have ha : Adjacent .west q r := ⟨by change q.1.val - 1 + 1 = q.1.val; omega, rfl⟩
  have hoff : r ∉ Support.streets (l.streetColumnSet p) (l.workingRowSet p) := by
    rintro (hc | hr)
    · have he := l.streetColumnSet_even p hc
      change (q.1.val - 1) % 2 = 0 at he
      omega
    · exact hrow hr
  exact ⟨r, ha, off_page_blocker l p hl (fun h => hoff (pages_subset_streets l p hl h))⟩

private theorem tail_west_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateTails p) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  obtain ⟨_, middle, hi, hx, v, _, hvm, hy⟩ := gate_tail_data l p hq
  have hs := gate_special_span p hx
  have hx0 := readLength_add_lt_x p middle 0
  have hxpos : 0 < q.1.val := by omega
  have hcol : q.1 ∈ l.streetColumnSet p := by
    change q.1.val ∈ streetColumns l (coordinates p)
    exact pageColumn_mem_street l p hl .lower (l.gateSpecialColumn_mem_page p hi hx)
  have heven := l.streetColumnSet_even p hcol
  exact gate_west_background l p hl hxpos heven (tail_not_row l p hq)

private theorem tail_marker_ray (l : PortLayout) (p : Scales.Parameters)
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hmarkers : l.gateInterlevelMarkers p ⊆ G)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateTails p) : Freeze.Ray (l.gateTails p) G .north q := by
  obtain ⟨hlevels, middle, hi, hx, v, hv, hvm, hy⟩ := gate_tail_data l p hq
  have hm := readDepth_le_last p 1
  have hn := readDepth_le_last p 2
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  let n := gateMarkerDepth p - v - 1
  let path : Fin (n + 2) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (q.1, ⟨p.H - (v + i.val), by have := q.2.isLt; omega⟩)
  have hstart : path 0 = q := by
    apply Prod.ext
    · rfl
    · apply Fin.ext
      change p.H - (v + 0) = q.2.val
      simpa only [Nat.add_zero] using hy.symm
  rw [← hstart]
  apply Freeze.Ray.of_path path
  · intro i
    have hi := i.isLt
    simp only [path, Adjacent, Fin.val_succ, Fin.val_castSucc]
    constructor
    · trivial
    · dsimp only [n, gateMarkerDepth] at hi hvm
      omega
  · intro i
    left
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hlevels, middle, hi, hx, v + (i.val + 1), by omega, ?_, rfl⟩
    have hi := i.isLt
    dsimp only [n] at hi
    omega
  · apply hmarkers
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hlevels, middle, hi, hx, ?_⟩
    change p.H - (v + (n + 1)) = p.H - gateMarkerDepth p
    dsimp only [n]
    congr 1
    omega

/-- Actual page blockers and actual special-column marker holes anchor every full gate tail. -/
theorem gateTails_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hmarkers : l.gateInterlevelMarkers p ⊆ G) : Freeze.Anchored (l.gateTails p) G := by
  intro d q hq
  have hv := tail_marker_ray l p hmarkers hq
  obtain ⟨r, ha, hr⟩ := tail_west_blocker l p hl hq
  have hh : Freeze.Ray (l.gateTails p) G .west q := .hit ha (hpage hr)
  cases d with
  | north => exact Or.inl hv
  | south => exact Or.inr hv
  | east => exact Or.inr hh
  | west => exact Or.inl hh

/-- The actual next-depth gate cells lie in the computed tails, or directly in the
central auxiliary closure when the gate is on the only allocated level. -/
theorem gateTails_deep_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ gateSpecialColumns p middle)
    (hy : q.2.val = p.H - (readDepth p 1 + 3)) :
    q ∈ (l.pageFrozenBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateTails p := by
  by_cases hlevels : 1 < p.levels
  · apply Finset.mem_union_right
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, hlevels, middle, hi, hx, readDepth p 1 + 3, le_rfl, ?_, hy⟩
    have hg := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
    dsimp only [gateMarkerDepth]
    simp only [Nat.reduceAdd] at hg
    omega
  · have hM : p.levels = 1 := by have := p.levels_pos; omega
    have hY := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    have hd : readDepth p 1 = p.Y p.levels := by rw [hM, readDepth_eq p (by omega) (by omega)]
    have hcol : q.1 ∈ l.streetColumnSet p := by
      change q.1.val ∈ streetColumns l (coordinates p)
      exact pageColumn_mem_street l p hl .lower (l.gateSpecialColumn_mem_page p hi hx)
    have hmain := l.gateSpecialColumn_not_main p hl ha hi hx
    have hc : q ∉ l.centralMarkers p := by
      intro hc
      have hb := (Finset.mem_filter.mp hc).2
      omega
    have hbox : q ∈ l.centralAuxiliaryBoxes p :=
      (mem_centralAuxiliaryBoxes l p q).mpr ⟨hcol, hmain, by omega, by omega, hc⟩
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_union_left _ (Finset.mem_union_right _ hbox))))

/-- One computed closure freezes every actual gate-column tail. -/
theorem gateTails_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p)
      ((l.pageFrozenBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateTails p) :=
  .add ((l.pageBackground_closure p hl hM ha initial target).adjoin_blockers (l.gateInterlevelMarkers p))
    (l.gateTails_initial_full p hl hM ha initial target)
    (l.gateTails_anchored p hl _ Finset.subset_union_left Finset.subset_union_right)

end PushPuzzle.PushS.PortLayout

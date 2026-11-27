/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateTails
public import PushS.PortGateWide
import all PushS.PortGateTails
import all PushS.PortGatePageWindow
import all PushS.PortGateWide
import all PushS.PortEndpointRWall
import all PushS.PortPageBackground
import all PushS.PortStreetSupport
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! The actual bottom work-row bars and four public-column caps of a three-port gate. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def BottomPosition (p : Scales.Parameters) (middle : ℕ) (q : ℕ × ℕ) : Prop :=
  (q.1 ∈ gatePublicColumns p middle ∧ q.2 = p.H - (readDepth p 1 + 1)) ∨
    (q.2 = p.H - (readDepth p 1 + 2) ∧ (q.1 < p.x middle ∨ p.x middle + 4 < q.1))

private def BottomRow (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2.val = p.H - (readDepth p 1 + 2) ∧
    ((left.cell.1.val ≤ q.1.val ∧ q.1.val < p.x middle) ∨
      (p.x middle + 4 < q.1.val ∧ q.1.val ≤ right.cell.1.val))

/-- Two actual bottom bars and the four public caps; private branch cells are outside this region. -/
noncomputable def gateBottomWall (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
    ((q.1.val ∈ gatePublicColumns p middle ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
      BottomRow l p middle left right q)

private theorem bottom_data (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateBottomWall p middle left right) :
    q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
      ((q.1.val ∈ gatePublicColumns p middle ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
        BottomRow l p middle left right q) := by
  classical
  simpa only [gateBottomWall, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem bottom_source_clear (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle : ℕ} {q : ℕ × ℕ} (hpos : BottomPosition p middle q)
    (hsource : GateHoleSource l p state middle q) : False := by
  have hx0 := readLength_add_lt_x p middle 0
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hrow : q.2 = p.H - (readDepth p 1 + 1) ∨ q.2 = p.H - (readDepth p 1 + 2) :=
    hpos.elim (fun h => Or.inl h.2) (fun h => Or.inr h.1)
  have hna : q.1 ≠ p.x middle := by
    rcases hpos with ⟨hx, _⟩ | ⟨_, hx⟩
    · simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · omega
  have hprivate : ¬(q.1 = p.x middle + 4 ∧ q.2 = p.H - (readDepth p 1 + 1)) := by
    rcases hpos with ⟨hx, _⟩ | ⟨hy, hx⟩
    · simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
      omega
    · omega
  have hbranch : ¬(q.2 = p.H - (readDepth p 1 + 2) ∧ p.x middle + 1 ≤ q.1 ∧ q.1 ≤ p.x middle + 4) := by
    rcases hpos with ⟨_, hy⟩ | ⟨_, hx⟩ <;> omega
  cases hsource with
  | fixed hfixed =>
    cases gateFixedSegments_location p middle hfixed with
    | publicStreet _ hr => omega
    | privateCap hx hy => exact hprivate ⟨hx, hy⟩
    | privateBranch hy hx => exact hbranch ⟨hy, hx⟩
    | halfDepth hr => omega
    | marker hlevels _ hr =>
      have hgap := readDepth_interlevel_margin p (show 1 ≤ 1 by omega) hlevels
      have hnext := readDepth_add_lt_H p 2
      simp only [Nat.reduceAdd] at hgap
      omega
  | @signal kind first internal _ hcenter hsignal =>
    cases gateSegments_location p state kind first internal hsignal with
    | horizontal hr => omega
    | axis hx _ => exact hna (by simpa only [hcenter] using hx)

private theorem bottom_row_columns (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : BottomRow l p middle left right q)
    (hc : q.1 ∈ l.pageColumnSet p .lower) : q.1.val ∈ gatePublicColumns p middle := by
  have hx0 := readLength_add_lt_x p middle 0
  have hs : q.1.val ∈ gateSpecialColumns p middle := by
    rcases hq.2 with hl | hr
    · exact left.columns _ hc hl
    · exact right.columns _ hc ⟨by omega, hr.2⟩
  have hfour : q.1.val ≠ p.x middle + 4 := by
    rcases hq.2 with hl | hr <;> omega
  change q.1.val ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false]
  tauto

/-- Every cell of the concrete gate bottom wall is occupied in every actual initial encoding. -/
theorem gateBottomWall_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true) :
    l.gateBottomWall p middle left right ⊆
      (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hcm, hw, hq⟩ := bottom_data l p middle left right hq
  have hpos : BottomPosition p middle (q.1.val, q.2.val) := by
    rcases hq with hcap | hrow
    · exact Or.inl hcap
    · exact Or.inr ⟨hrow.1, hrow.2.imp (fun h => h.2) (fun h => h.1)⟩
  by_cases hnear : Nat.dist q.1.val (p.x middle) ≤ p.L p.levels + 16
  · have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
    have hD := readDepth_add_lt_D p 1
    have hH : p.H = 2 * p.D := rfl
    have hwindow : q ∈ gatePageWindow p middle := by
      refine ⟨?_, hnear⟩
      rcases hpos with ⟨_, hy⟩ | ⟨hy, _⟩ <;> constructor <;> omega
    by_contra hbox
    have hh := (mem_holes _).mpr hbox
    rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
    exact bottom_source_clear l p initial hpos (l.encodedSegments_gatePageWindow p hl hM ha initial hi hwindow hh)
  · rcases hq with hcap | hrow
    · have hs := gate_special_span p (gatePublicColumn_mem_special p hcap.1)
      simp only [Nat.dist] at hnear
      omega
    · refine l.encodedSegments_far_from_axes_full p hl hM initial _
        (l.physicalInstance_initial_holes p hl hM ha initial target) ?_ hcm hw ?_
      · rcases hrow.2 with hleft | hright
        · exact l.gateWideSeparator_interval_off_frame p hl ha hi left hrow.1 hleft
        · exact l.gateWideSeparator_interval_off_frame p hl ha hi right hrow.1 ⟨by omega, hright.2⟩
      · rcases hrow.2 with hleft | hright
        · exact l.gateWideSeparator_interval_far_axes p hl ha hi left hleft (by omega)
        · exact l.gateWideSeparator_interval_far_axes p hl ha hi right ⟨by omega, hright.2⟩ (by omega)

private theorem bottom_point (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (middle : ℕ) (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hpage : l.pageFrozenBlockers p hl ⊆ G)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val ∈ gatePublicColumns p middle ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
      BottomRow l p middle left right q) : q ∈ l.gateBottomWall p middle left right ∨ q ∈ G := by
  by_cases hm : q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p
  · exact Or.inr (hpage (marker_blocker l p hl hm))
  · left
    classical
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (not_or.mp hm).1, (not_or.mp hm).2, hq⟩

private def bottomCell (p : Scales.Parameters) (x : Fin (p.W + 1)) (k : ℕ) :
    Cell (p.W + 1) (p.H + 1) := (x, ⟨p.H - (readDepth p 1 + k), by omega⟩)

private theorem public_bottom_row (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ gatePublicColumns p middle) :
    BottomRow l p middle left right (bottomCell p q.1 2) := by
  refine ⟨rfl, ?_⟩
  have hl := left.outside
  have hr := right.outside
  have hm := readLength_add_lt_x p middle 0
  simp only [Bool.false_eq_true, ite_true, ite_false] at hl hr
  simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
  dsimp only [bottomCell]
  omega

private theorem bottom_vertical (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (middle : ℕ) (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val ∈ gateSpecialColumns p middle →
      q.2.val = p.H - (readDepth p 1 + 3) → q ∈ G)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val ∈ gatePublicColumns p middle ∧ q.2.val = p.H - (readDepth p 1 + 1)) ∨
      BottomRow l p middle left right q) :
    Freeze.Ray (l.gateBottomWall p middle left right) G .north q := by
  let far := bottomCell p q.1 3
  have hY := readDepth_add_lt_H p 1
  rcases hq with hcap | hrow
  · let mid := bottomCell p q.1 2
    have hf : far ∈ G := hdeep far (gatePublicColumn_mem_special p hcap.1) rfl
    have hy := hcap.2
    have ha : Adjacent .north q mid := by
      simp only [Adjacent, mid, bottomCell]
      exact ⟨trivial, by omega⟩
    have hb : Adjacent .north mid far := by
      simp only [Adjacent, mid, far, bottomCell]
      exact ⟨trivial, by omega⟩
    rcases bottom_point l p hl middle left right hpage (Or.inr (public_bottom_row l p middle left right hcap.1)) with hm | hg
    · exact .extend ha hm (.hit hb hf)
    · exact .hit ha hg
  · by_cases hc : q.1 ∈ l.pageColumnSet p .lower
    · have hf : far ∈ G := hdeep far
        (gatePublicColumn_mem_special p (bottom_row_columns l p left right (q := q) hrow hc)) rfl
      have hy := hrow.1
      refine .hit ?_ hf
      simp only [Adjacent, far, bottomCell]
      exact ⟨trivial, by omega⟩
    · obtain ⟨r, ha, hr⟩ := l.workingRow_north_blocker p hl .lower
        ((l.workingDepthCoordinates_mem p 0 (by have := p.levels_pos; omega)).2) q hrow.1 hc
      exact .hit ha (hpage hr)

private theorem bottom_cap_west (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ gatePublicColumns p middle)
    (hy : q.2.val = p.H - (readDepth p 1 + 1)) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hc : q.1 ∈ l.streetColumnSet p := by
    change q.1.val ∈ streetColumns l (coordinates p)
    exact pageColumn_mem_street l p hl .lower
      (l.gateSpecialColumn_mem_page p hi (gatePublicColumn_mem_special p hx))
  have heven := l.streetColumnSet_even p hc
  have hspan := gate_special_span p (gatePublicColumn_mem_special p hx)
  have hx0 := readLength_add_lt_x p middle 0
  have hpos : 0 < q.1.val := by omega
  apply gate_west_background l p hl hpos heven
  intro hr
  have he := l.workingRowSet_even p hr
  have hD := readDepth_add_lt_H p 1
  have hY := readDepth_even p 1
  have hH := H_even p
  change q.2.val % 2 = 0 at he
  omega

/-- The concrete page and deep-column anchors freeze the two bottom bars and four public caps. -/
theorem gateBottomWall_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hdeep : ∀ q : Cell (p.W + 1) (p.H + 1), q.1.val ∈ gateSpecialColumns p middle →
      q.2.val = p.H - (readDepth p 1 + 3) → q ∈ G) :
    Freeze.Anchored (l.gateBottomWall p middle left right) G := by
  intro d q hq
  obtain ⟨_, hw, hq⟩ := bottom_data l p middle left right hq
  have hv := bottom_vertical l p hl middle left right hpage hdeep hq
  have hh : Freeze.Ray (l.gateBottomWall p middle left right) G .east q ∨
      Freeze.Ray (l.gateBottomWall p middle left right) G .west q := by
    rcases hq with hcap | ⟨hy, hleft | hright⟩
    · obtain ⟨r, ha, hr⟩ := bottom_cap_west l p hl hi hcap.1 hcap.2
      exact Or.inr (.hit ha (hpage hr))
    · have hn : q.1.val ≠ left.cell.1.val := by
        intro hx
        exact hw ((Prod.ext (Fin.ext hx) (Fin.ext (hy.trans left.row.symm))).symm ▸ left.hole)
      apply Or.inr
      apply Freeze.Ray.west_of_interval (Fin.ext (hy.trans left.row.symm)) (by omega)
        (hpage (marker_blocker l p hl (Or.inr left.hole)))
      intro r hr hlo hhi
      apply bottom_point l p hl middle left right hpage
      exact Or.inr ⟨(congrArg Fin.val hr).trans hy, Or.inl ⟨by omega, by omega⟩⟩
    · have hn : q.1.val ≠ right.cell.1.val := by
        intro hx
        exact hw ((Prod.ext (Fin.ext hx) (Fin.ext (hy.trans right.row.symm))).symm ▸ right.hole)
      apply Or.inl
      apply Freeze.Ray.east_of_interval (Fin.ext (hy.trans right.row.symm)) (by omega)
        (hpage (marker_blocker l p hl (Or.inr right.hole)))
      intro r hr hlo hhi
      apply bottom_point l p hl middle left right hpage
      exact Or.inr ⟨(congrArg Fin.val hr).trans hy, Or.inr ⟨by omega, by omega⟩⟩
  cases d with
  | north => exact Or.inl hv
  | south => exact Or.inr hv
  | east => exact hh
  | west => exact hh.symm

/-- Every actual public gate-column cap lies in the computed wall or existing page blockers. -/
theorem gateBottomWall_cap_mem (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (middle : ℕ) (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ gatePublicColumns p middle)
    (hy : q.2.val = p.H - (readDepth p 1 + 1)) :
    q ∈ l.pageFrozenBlockers p hl ∪ l.gateBottomWall p middle left right :=
  Finset.mem_union.mpr (bottom_point l p hl middle left right (fun _ h => h) (Or.inl ⟨hx, hy⟩)).symm

/-- One actual finite closure attaches both bottom bars and all four public caps after the tails. -/
theorem gateBottomWall_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    (left : GateWideSeparator l p middle false) (right : GateWideSeparator l p middle true) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p)
      (((l.pageFrozenBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateTails p) ∪
        l.gateBottomWall p middle left right) :=
  .add (l.gateTails_closure p hl hM ha initial target)
    (l.gateBottomWall_initial_full p hl hM ha initial target hi left right)
    (l.gateBottomWall_anchored p hl hi left right _
      (fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ h))
      (fun _ hx hy => l.gateTails_deep_mem p hl ha hi hx hy))

end PushPuzzle.PushS.PortLayout

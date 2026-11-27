/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortEndpointOuterWide
public import PushS.PortEndpointLocality
public import PushS.PortEndpointPageWindow
public import PushS.PortAxisLocality
public import PushS.PortPageClosure
import all PushS.PortEndpointLocality
import all PushS.PortEndpointSeparation
import all PushS.PortCentralStrip
import all PushS.PortStreetSupport
import all PushS.PortStreetSeparation
import all PushS.PortSignalLocality
import all PushS.PortEndpointCrossing
import all PushS.PortWideGeometry
import all PushS.PortPageBackground
import all PushS.PortSegments

/-! Concrete full outer rows attached to the actual endpoint wide separators. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def OuterRow (p : Scales.Parameters) (e : Endpoint)
    (g q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2 = g.2 ∧ (if e.inward then g.1.val ≤ q.1.val ∧ q.1.val < p.x e.port - readLength p e.level
    else p.x e.port + readLength p e.level < q.1.val ∧ q.1.val ≤ g.1.val)

/-- Full cells between an ordinary endpoint's f street and its actual outer separator.
Permanent central and wide holes remain in the established blocker set. -/
noncomputable def endpointOuterWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) : Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
    OuterRow p e g.cell q

private theorem mem_endpointOuterWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.endpointOuterWall p e g ↔ q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
      OuterRow p e g.cell q := by
  classical
  simp only [endpointOuterWall, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem own_fixed_span (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    if e.inward then p.x e.port - readLength p e.level ≤ q.1 ∧ q.1 ≤ p.x e.port + 2
      else p.x e.port - 2 ≤ q.1 ∧ q.1 ≤ p.x e.port + readLength p e.level := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hL : 16384 ≤ (coordinates p).length e.level := readLength_ge p hj hm
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  change if e.inward then (coordinates p).x e.port - (coordinates p).length e.level ≤ q.1 ∧
      q.1 ≤ (coordinates p).x e.port + 2
    else (coordinates p).x e.port - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x e.port + (coordinates p).length e.level
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hp := (vertical_coordinates hq).1
    cases hd : e.inward <;> simp [auxiliary, outward, hd] at hp ⊢ <;> omega
  · have hp := (vertical_coordinates hq).1
    cases hd : e.inward <;> simp [auxiliary, inward, hd] at hp ⊢ <;> omega
  · have hp := (horizontal_coordinates hq).2
    cases hd : e.inward <;> simp [auxiliary, inward, outward, hd] at hp ⊢ <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    all_goals split at hs
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    all_goals subst s
    all_goals have hp := (point_coordinates hq).1
    all_goals cases hd : e.inward <;> simp [auxiliary, inward, outward, hd] at hp ⊢ <;> omega
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals have hp := (point_coordinates hq).1
      all_goals cases hd : e.inward <;> simp [auxiliary, inward, outward, hd] at hp ⊢ <;> omega
    · cases hs

private theorem outer_window_not_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {e : Endpoint} (he : e ∈ l.endpoints)
    {q : Cell (p.W + 1) (p.H + 1)} (hw : q ∈ endpointPageWindow p e)
    (hout : if e.inward then q.1.val < p.x e.port - readLength p e.level
      else p.x e.port + readLength p e.level < q.1.val) :
    q ∉ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  rw [l.encodedSegments_endpointPageWindow p hl hM ha state e he q hw]
  intro hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hs | hs
  · have hb := own_fixed_span l p hl hM he ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb hout <;> omega
  · have hb := endpoint_near p state e ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
    obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
    have hL := readLength_ge p hj hm
    have hc : (coordinates p).x e.port = p.x e.port := rfl
    cases hd : e.inward <;>
      simp only [hd, Bool.false_eq_true, ite_true, ite_false, hc] at hb hout <;> omega

private theorem outer_row_off_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : OuterRow p e g.cell q) : q ∉ Boundary.frame := by
  have hgf := l.wideSeparatorHoles_off_frame p hl g.hole
  have hx0 := readLength_add_lt_x p e.port e.level
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) e.level
  have hr := congrArg Fin.val hq.1
  have hb := hq.2
  have hgx := g.cell.1.isLt
  have hqx := q.1.isLt
  cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb
  all_goals
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hgf ⊢
    omega

private theorem outer_row_far_axes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) {v : ℕ}
    (g : EndpointOuterWideSeparator l p e v)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : OuterRow p e g.cell q)
    (hfar : p.L p.levels + 16 < Nat.dist q.1.val (p.x e.port)) :
    ∀ i < l.portCount, p.L p.levels + 12 < Nat.dist q.1.val (p.x i) := by
  have hlen := readLength_le_last p e.level
  intro i hi
  have hm := x_add_readLength_lt_W p (show i < p.axes by omega) 0
  let x : Fin (p.W + 1) := ⟨p.x i, by omega⟩
  have hx : x ∈ l.streetColumnSet p := axis_column l p hi
  have hwide := l.wideSeparatorHoles_street_gap p hl g.hole x hx
  have hbudget := local_radius_budget p p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hbudget
  have hno := g.columnsEmpty (p.x i) (axis_in_pageColumns l p hl e.side hi)
  have hb := hq.2
  have hD := p.outer_distance
  by_cases hie : i = e.port
  · rw [hie]
    omega
  · rcases lt_or_gt_of_ne hie with hie | hie
    all_goals have hspace := axis_spacing p hie
    all_goals cases hd : e.inward <;>
      simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hno hb <;>
      simp only [Nat.dist, x] at hwide hfar ⊢ <;> omega

/-- The actual selected outer row of every ordinary endpoint starts full for every signal state. -/
theorem endpointOuterWall_initial_full_general (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p) :
    l.endpointOuterWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hc, hw, hrow⟩ := (mem_endpointOuterWall l p e g q).mp hq
  by_cases hx : Nat.dist q.1.val (p.x e.port) ≤ p.L p.levels + 16
  · have hwindow := l.endpointPageWindow_of_workingDepth p e hv q
      ((congrArg Fin.val hrow.1).trans g.row) hx
    have hout : if e.inward then q.1.val < p.x e.port - readLength p e.level
        else p.x e.port + readLength p e.level < q.1.val := by
      have hb := hrow.2
      cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hb ⊢ <;> omega
    have hnot := outer_window_not_hole l p hl hM ha initial he hwindow hout
    change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜ
    exact Finset.mem_compl.mpr hnot
  · apply l.encodedSegments_far_from_axes_full p hl hM initial _
      (l.physicalInstance_initial_holes p hl hM ha initial target)
      (outer_row_off_frame l p hl ha e he g hrow) hc hw
    exact outer_row_far_axes l p hl ha e g hrow (by omega)

/-- The selected outer row is initially full at the last allocated endpoint level. -/
theorem endpointOuterWall_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p)
    (_heM : e.level = p.levels) :
    l.endpointOuterWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes :=
  l.endpointOuterWall_initial_full_general p hl hM ha initial target e he g hv

private theorem marker_outer_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p) :
    q ∈ l.pageFrozenBlockers p hl :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union.mpr hq))

private theorem outer_row_point (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) {v : ℕ} (g : EndpointOuterWideSeparator l p e v)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : OuterRow p e g.cell q) :
    q ∈ l.endpointOuterWall p e g ∨ q ∈ l.pageFrozenBlockers p hl := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact Or.inr (marker_outer_blocker l p hl (Or.inl hc))
  · by_cases hw : q ∈ l.wideSeparatorHoles p
    · exact Or.inr (marker_outer_blocker l p hl (Or.inr hw))
    · exact Or.inl ((mem_endpointOuterWall l p e g q).mpr ⟨hc, hw, hq⟩)

private theorem outer_row_north_blocker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (e : Endpoint) {v : ℕ} (g : EndpointOuterWideSeparator l p e v)
    (hv : v ∈ l.workingDepthCoordinates p) (q : Cell (p.W + 1) (p.H + 1))
    (hq : OuterRow p e g.cell q) :
    ∃ r, Adjacent .north q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  apply l.workingRow_north_blocker p hl e.side hv q ((congrArg Fin.val hq.1).trans g.row)
  exact fun hc => g.columnsEmpty _ hc hq.2

/-- Every outer-wall component has a horizontal wide-hole anchor and a vertical
page-background anchor. -/
theorem endpointOuterWall_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (e : Endpoint) {v : ℕ} (g : EndpointOuterWideSeparator l p e v)
    (hv : v ∈ l.workingDepthCoordinates p) :
    Freeze.Anchored (l.endpointOuterWall p e g) (l.pageFrozenBlockers p hl) := by
  intro d q hq
  obtain ⟨_, hw, hrow⟩ := (mem_endpointOuterWall l p e g q).mp hq
  obtain ⟨r, ha, hr⟩ := outer_row_north_blocker l p hl e g hv q hrow
  have hv : Freeze.Ray (l.endpointOuterWall p e g) (l.pageFrozenBlockers p hl) .north q := .hit ha hr
  have hh : Freeze.Ray (l.endpointOuterWall p e g) (l.pageFrozenBlockers p hl) .east q ∨
      Freeze.Ray (l.endpointOuterWall p e g) (l.pageFrozenBlockers p hl) .west q := by
    have hneq : q.1.val ≠ g.cell.1.val :=
      fun hx => hw ((Prod.ext (Fin.ext hx) hrow.1).symm ▸ g.hole)
    have hb := hrow.2
    have hg := marker_outer_blocker l p hl (Or.inr g.hole)
    cases hd : e.inward with
    | false =>
      simp only [hd, Bool.false_eq_true, ite_false] at hb
      apply Or.inl
      apply Freeze.Ray.east_of_interval hrow.1 (by omega) hg
      intro s hy hx hxg
      apply outer_row_point l p hl e g s
      refine ⟨hy.trans hrow.1, ?_⟩
      simp only [hd, Bool.false_eq_true, ite_false]
      omega
    | true =>
      simp only [hd, ite_true] at hb
      apply Or.inr
      apply Freeze.Ray.west_of_interval hrow.1 (by omega) hg
      intro s hy hxg hx
      apply outer_row_point l p hl e g s
      refine ⟨hy.trans hrow.1, ?_⟩
      simp only [hd, ite_true]
      omega
  cases d with
  | north => exact Or.inl hv
  | south => exact Or.inr hv
  | east => exact hh
  | west => exact hh.symm

/-- A last-level endpoint's outer wall extends the actual page freezing closure. -/
theorem endpointOuterWall_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointOuterWideSeparator l p e v) (hv : v ∈ l.workingDepthCoordinates p)
    (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.pageFrozenBlockers p hl ∪ l.endpointOuterWall p e g) :=
  .add (l.pageBackground_closure p hl hM ha initial target)
    (l.endpointOuterWall_initial_full p hl hM ha initial target e he g hv heM)
    (l.endpointOuterWall_anchored p hl e g hv)

end PushPuzzle.PushS.PortLayout

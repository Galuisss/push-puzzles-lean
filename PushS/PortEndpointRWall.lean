/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortAxisLocality
public import PushS.PortEndpointCaps
public import PushS.PortEndpointWide
public import PushS.PortPageClosure
public import PushS.EndpointWalking
import all PushS.EndpointWalking
import all PushS.PortSegments
import all PushS.PortAxisClear
import all PushS.PortCentralFreeze
import all PushS.PortCentralStrip
import all PushS.PortPageBackground
import all PushS.PortEndpointLocality
import all PushS.PortSignalLocality
import all PushS.PortStreetSeparation
import all PushS.PortStreetSupport
import all PushS.PortSegmentBounds

/-! Concrete inward walls at ordinary endpoints on the last working level. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

private abbrev rColumn (p : Scales.Parameters) (e : Endpoint) : ℕ :=
  if e.inward then p.x e.port + 2 else p.x e.port - 2

private def InwardRow (p : Scales.Parameters) (e : Endpoint)
    (g q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2 = g.2 ∧ (if e.inward then p.x e.port < q.1.val ∧ q.1.val ≤ g.1.val
    else g.1.val ≤ q.1.val ∧ q.1.val < p.x e.port)

/-- The inward full row up to its actual wide separator, together with the r cell one depth
beyond the work row. Existing permanent holes are kept out of the full region. -/
noncomputable def endpointRWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e) : Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
    ((q.1.val = rColumn p e ∧ q.2.val =
      (if e.side = .upper then p.Y p.levels + 1 else p.H - (p.Y p.levels + 1))) ∨
      InwardRow p e g.cell q)

private theorem mem_endpointRWall (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e) (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ l.endpointRWall p e g ↔ q ∉ l.centralMarkers p ∧ q ∉ l.wideSeparatorHoles p ∧
      ((q.1.val = rColumn p e ∧ q.2.val =
        (if e.side = .upper then p.Y p.levels + 1 else p.H - (p.Y p.levels + 1))) ∨
        InwardRow p e g.cell q) := by
  classical
  simp only [endpointRWall, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem last_read_depth (p : Scales.Parameters) {e : Endpoint} (he : e.level = p.levels) :
    readDepth p e.level = p.Y p.levels := by rw [he, readDepth_eq p p.levels_pos le_rfl]

private theorem inward_row_window (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : InwardRow p e g.cell q)
    (hx : Nat.dist q.1.val (p.x e.port) ≤ readLength p e.level + 16) :
    q ∈ endpointInwardCap p e := by
  have hd := last_read_depth p heM
  have hy := congrArg Fin.val hq.1
  rw [g.row] at hy
  have hmargin := readDepth_add_lt_H p e.level
  change readDepth p e.level + 64 < p.H at hmargin
  have hin : if e.inward then p.x e.port < q.1.val else q.1.val < p.x e.port := by
    have hb := hq.2
    cases hs : e.inward <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hb ⊢ <;> omega
  refine ⟨⟨?_, hx⟩, Or.inr ⟨?_, hin⟩⟩
  · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, hd] at * <;> omega
  · simpa only [hd] using hy

private theorem inward_row_off_frame (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : InwardRow p e g.cell q) : q ∉ Boundary.frame := by
  have hgf := l.wideSeparatorHoles_off_frame p hl g.hole
  have hx := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p (show e.port < p.axes by
    have := l.endpoints_port_lt hl he; omega) 0
  intro hf
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
  cases d with
  | north =>
    apply hgf ((Boundary.mem_frame g.cell).mpr ⟨.north, ?_⟩)
    simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hq.1] using hd
  | south =>
    apply hgf ((Boundary.mem_frame g.cell).mpr ⟨.south, ?_⟩)
    simpa only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and, hq.1] using hd
  | east =>
    have heq : g.cell.1.val ≠ p.W := by
      intro heq
      exact hgf ((Boundary.mem_frame g.cell).mpr ⟨.east, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩)
    have hqb := hq.2
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at hqb <;>
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;>
      have := g.cell.1.isLt <;> omega
  | west =>
    have heq : g.cell.1.val ≠ 0 := by
      intro heq
      exact hgf ((Boundary.mem_frame g.cell).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, heq⟩⟩)
    have hqb := hq.2
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_false, ite_true] at hqb <;>
      simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega

private theorem wide_axis_gap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {e : Endpoint} (g : EndpointWideSeparator l p e) (i : ℕ) (hi : i < l.portCount) :
    p.L p.levels + 12 < Nat.dist g.cell.1.val (p.x i) := by
  have hbound := x_add_readLength_lt_W p (show i < p.axes by omega) 0
  let x : Fin (p.W + 1) := ⟨p.x i, by omega⟩
  have hx : x ∈ l.streetColumnSet p := axis_column l p hi
  have hgap := l.wideSeparatorHoles_street_gap p hl g.hole x hx
  have hbudget := local_radius_budget p p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hbudget
  dsimp only [x] at hgap
  omega

private theorem inward_row_far_axes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : InwardRow p e g.cell q)
    (hfar : readLength p e.level + 16 < Nat.dist q.1.val (p.x e.port)) :
    ∀ i < l.portCount, p.L p.levels + 12 < Nat.dist q.1.val (p.x i) := by
  rw [heM, readLength_eq p p.levels_pos le_rfl] at hfar
  intro i hi
  have hwide := wide_axis_gap l p hl ha g i hi
  have hcol := axis_in_pageColumns l p hl e.side hi
  have hnr : rColumn p e ≠ p.x i :=
    auxiliary_off_axis l p hl hM he i (Or.inr rfl)
  have hno : ¬(if e.inward then p.x e.port < p.x i ∧ p.x i ≤ g.cell.1.val
      else g.cell.1.val ≤ p.x i ∧ p.x i < p.x e.port) := by
    intro hc
    exact hnr (g.columns _ hcol hc).symm
  have hqb := hq.2
  cases hs : e.inward <;> simp only [hs, Bool.false_eq_true, ite_false, ite_true] at hno hqb <;>
    simp only [Nat.dist] at hfar hwide ⊢ <;> omega

/-- The actual last-level inward r wall starts full for every physical signal state. -/
theorem endpointRWall_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels) :
    l.endpointRWall p e g ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hq
  obtain ⟨hc, hw, hq⟩ := (mem_endpointRWall l p e g q).mp hq
  rcases hq with hcap | hrow
  · apply l.physicalInstance_endpoint_cap_full p hl hM ha initial target e he
    have hd := last_read_depth p heM
    have hlen := readLength_add_lt_x p e.port 0
    have hy := readDepth_add_lt_H p e.level
    have hg := readDepth_ge p (j := e.level) (by rw [heM]; exact p.levels_pos) (by rw [heM])
    refine ⟨⟨?_, ?_⟩, Or.inl ?_⟩
    · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, hd] at * <;> omega
    · have hx := hcap.1
      cases hs : e.inward <;> simp only [rColumn, hs, Bool.false_eq_true, ite_false, ite_true] at hx <;>
        simp only [Nat.dist] <;> omega
    · simpa only [hd] using hcap
  · by_cases hx : Nat.dist q.1.val (p.x e.port) ≤ readLength p e.level + 16
    · exact l.physicalInstance_endpoint_cap_full p hl hM ha initial target e he (inward_row_window l p e g heM hrow hx)
    · apply l.encodedSegments_far_from_axes_full p hl hM initial _
        (l.physicalInstance_initial_holes p hl hM ha initial target)
        (inward_row_off_frame l p hl ha e he g hrow) hc hw
      exact inward_row_far_axes l p hl hM ha e he g heM hrow (by omega)

private theorem marker_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p) :
    q ∈ l.pageFrozenBlockers p hl :=
  Finset.mem_union_left _ (Finset.mem_union_left _ ((Finset.mem_union.mpr hq)))

private theorem off_page_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∉ (l.twoPageStreets p hl).support) :
    q ∈ l.pageFrozenBlockers p hl := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact marker_blocker l p hl (Or.inl hc)
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((l.mem_pageBackgroundBoxes p hl q).mpr ⟨hq, hc⟩))

/-- One cell beyond a last-level public f/r corridor lies in the frozen central column. -/
theorem endpointStreet_deep_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) (k : EndpointStreet) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = k.column p e)
    (hy : q.2.val = if e.side = .upper then p.Y p.levels + 3 else p.H - (p.Y p.levels + 3)) :
    q ∈ l.pageFrozenBlockers p hl := by
  have hdep := last_read_depth p heM
  have hwindow : q ∈ endpointWindow p e := by
    have hm := readDepth_add_lt_H p e.level
    have hx0 := readLength_add_lt_x p e.port e.level
    constructor
    · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false, hdep] at hy ⊢ <;> omega
    · rw [hx]
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, hd,
          Bool.false_eq_true, ite_false, ite_true, Nat.dist] <;> omega
  have hc := l.endpointWindow_not_central p e hwindow
  have hcol : q.1 ∈ l.streetColumnSet p := by
    rw [l.streetColumnSet_iff, hx]
    cases k
    · exact (auxiliary_columns l p he).1
    · exact (auxiliary_columns l p he).2
  have hmain : q.1 ∉ l.mainColumnSet p := by
    have hb := auxiliary_margin p e ((l.endpoints_port_lt hl he).trans_le ha)
    have hlo : 32 < k.column p e := by
      have hm := readLength_add_lt_x p e.port e.level
      cases k <;> cases hd : e.inward <;>
        simp only [EndpointStreet.column_f, EndpointStreet.column_r, hd,
          Bool.false_eq_true, ite_false, ite_true] <;> omega
    have hhi : k.column p e + 32 < p.W := by
      cases k with
      | f => exact hb.1
      | r => exact hb.2
    intro hm
    rcases (l.mainColumnSet_iff p q.1).mp hm with hm | hm | ⟨i, _, hm⟩
    · omega
    · omega
    · have haux : k.column p e = (auxiliary (coordinates p) e).1 ∨
          k.column p e = (auxiliary (coordinates p) e).2 := by cases k <;> simp [EndpointStreet.column]
      exact auxiliary_off_axis l p hl hM he i haux (hx.symm.trans hm)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hbox : q ∈ l.centralAuxiliaryBoxes p := by
    apply (mem_centralAuxiliaryBoxes l p q).mpr
    refine ⟨hcol, hmain, ?_, ?_, hc⟩
    all_goals cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hbox))

private theorem r_deep_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level = p.levels) {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = rColumn p e)
    (hy : q.2.val = onSide (coordinates p) e.side (p.Y p.levels + 3)) :
    q ∈ l.pageFrozenBlockers p hl :=
  l.endpointStreet_deep_blocker p hl hM ha e he heM .r hx hy

private theorem r_wall_row_point (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e) (q : Cell (p.W + 1) (p.H + 1))
    (hq : InwardRow p e g.cell q) : q ∈ l.endpointRWall p e g ∨ q ∈ l.pageFrozenBlockers p hl := by
  by_cases hc : q ∈ l.centralMarkers p
  · exact Or.inr (marker_blocker l p hl (Or.inl hc))
  · by_cases hw : q ∈ l.wideSeparatorHoles p
    · exact Or.inr (marker_blocker l p hl (Or.inr hw))
    · exact Or.inl ((mem_endpointRWall l p e g q).mpr ⟨hc, hw, Or.inr hq⟩)

private theorem east_r_wall_ray (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e) (he : e.inward = true)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : InwardRow p e g.cell q) (hx : q.1.val < g.cell.1.val) :
    Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .east q := by
  have hqb := hq.2
  simp only [he, ite_true] at hqb
  apply Freeze.Ray.east_of_interval hq.1 hx (marker_blocker l p hl (Or.inr g.hole))
  intro r hr hleft hright
  apply r_wall_row_point l p hl e g r
  exact ⟨hr.trans hq.1, by simp only [he, ite_true]; omega⟩

private theorem west_r_wall_ray (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (g : EndpointWideSeparator l p e) (he : e.inward = false)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : InwardRow p e g.cell q) (hx : g.cell.1.val < q.1.val) :
    Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .west q := by
  have hqb := hq.2
  simp only [he, Bool.false_eq_true, ite_false] at hqb
  apply Freeze.Ray.west_of_interval hq.1 hx (marker_blocker l p hl (Or.inr g.hole))
  intro r hr hleft hright
  apply r_wall_row_point l p hl e g r
  exact ⟨hr.trans hq.1, by simp only [he, Bool.false_eq_true, ite_false]; omega⟩

private def wallCell (p : Scales.Parameters) (side : Side) (x : Fin (p.W + 1)) (k : ℕ)
    (hk : k ≤ 3) : Cell (p.W + 1) (p.H + 1) :=
  (x, ⟨if side = .upper then p.Y p.levels + k else p.H - (p.Y p.levels + k), by
    have hY := last_depth_margin p
    have hH : p.H = 2 * p.D := rfl
    split <;> omega⟩)

private def depthDirection (side : Side) : Direction := if side = .upper then .south else .north

private theorem wallCell_side (p : Scales.Parameters) (side : Side) (x : Fin (p.W + 1))
    (k : ℕ) (hk : k ≤ 3) :
    if side = .upper then (wallCell p side x k hk).2.val < p.D
      else p.D < (wallCell p side x k hk).2.val := by
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  cases side <;> simp only [wallCell, reduceCtorEq, ite_false, ite_true] <;> omega

private theorem wallCell_one_not_row (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (g : EndpointWideSeparator l p e) (x : Fin (p.W + 1)) :
    (wallCell p e.side x 1 (by omega)).2 ∉ l.workingRowSet p := by
  have he := l.workingRowSet_even p (l.wideSeparatorHoles_working_row p g.hole)
  have hy := g.row
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  intro hr
  have her := l.workingRowSet_even p hr
  cases hs : e.side <;> simp only [wallCell, hs, reduceCtorEq, ite_false, ite_true] at hy her <;> omega

private theorem r_one_west_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (e : Endpoint) (he : e ∈ l.endpoints) (g : EndpointWideSeparator l p e)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = rColumn p e)
    (hy : q.2.val = if e.side = .upper then p.Y p.levels + 1 else p.H - (p.Y p.levels + 1)) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hcol : q.1 ∈ l.streetColumnSet p := by
    rw [l.streetColumnSet_iff, hx]
    exact (auxiliary_columns l p he).2
  have heven := l.streetColumnSet_even p hcol
  have hx0 : 0 < q.1.val := by
    have h := readLength_add_lt_x p e.port 0
    rw [hx]
    cases hs : e.inward <;> simp only [rColumn, hs, Bool.false_eq_true, ite_true, ite_false] <;> omega
  let r : Cell (p.W + 1) (p.H + 1) := (⟨q.1.val - 1, by have := q.1.isLt; omega⟩, q.2)
  have ha : Adjacent .west q r := ⟨by change q.1.val - 1 + 1 = q.1.val; omega, rfl⟩
  have hnc : r.1 ∉ l.streetColumnSet p := by
    intro hr
    have hn := l.streetColumnSet_even p hr
    dsimp only [r] at hn
    omega
  have hnr : r.2 ∉ l.workingRowSet p := by
    have heq : r.2 = (wallCell p e.side q.1 1 (by omega)).2 := Fin.ext hy
    rw [heq]
    exact wallCell_one_not_row l p e g q.1
  refine ⟨r, ha, off_page_blocker l p hl ?_⟩
  exact fun hp => (pages_subset_streets l p hl hp).elim hnc hnr

private theorem r_one_vertical_ray (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    (q : Cell (p.W + 1) (p.H + 1)) (hx : q.1.val = rColumn p e)
    (hy : q.2.val = if e.side = .upper then p.Y p.levels + 1 else p.H - (p.Y p.levels + 1)) :
    Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) (depthDirection e.side) q := by
  let mid := wallCell p e.side q.1 2 (by omega)
  let far := wallCell p e.side q.1 3 (by omega)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hadj : Adjacent (depthDirection e.side) q mid := by
    cases hs : e.side <;> simp only [depthDirection, wallCell, mid, Adjacent, hs,
      reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> constructor <;> first | trivial | omega
  have hadj' : Adjacent (depthDirection e.side) mid far := by
    cases hs : e.side <;> simp only [depthDirection, wallCell, mid, far, Adjacent, hs,
      reduceCtorEq, ite_true, ite_false] <;> constructor <;> first | trivial | omega
  have hfar : far ∈ l.pageFrozenBlockers p hl :=
    r_deep_blocker l p hl hM ha e he heM hx rfl
  have hmid : InwardRow p e g.cell mid := by
    refine ⟨Fin.ext g.row.symm, ?_⟩
    have hf := g.forward
    have hx0 := readLength_add_lt_x p e.port 0
    cases hs : e.inward <;> simp only [hs, Bool.false_eq_true, ite_true, ite_false] at hf ⊢ <;>
      dsimp only [mid, wallCell] <;> rw [hx] <;> dsimp only [rColumn] <;> simp only [hs, ite_true, ite_false, Bool.false_eq_true] <;> omega
  rcases r_wall_row_point l p hl e g mid hmid with hfull | hblock
  · exact .extend hadj hfull (.hit hadj' hfar)
  · exact .hit hadj hblock

private theorem r_row_vertical_ray (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)
    (q : Cell (p.W + 1) (p.H + 1)) (hq : InwardRow p e g.cell q) :
    Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .north q ∨
      Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .south q := by
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hrow := congrArg Fin.val hq.1
  rw [g.row] at hrow
  by_cases hx : q.1.val = rColumn p e
  · let far := wallCell p e.side q.1 3 (by omega)
    have hf : far ∈ l.pageFrozenBlockers p hl := r_deep_blocker l p hl hM ha e he heM hx rfl
    have ha' : Adjacent (depthDirection e.side) q far := by
      cases hs : e.side <;> simp only [depthDirection, wallCell, far, Adjacent, hs,
        reduceCtorEq, ite_true, ite_false] at hrow ⊢ <;> constructor <;> first | trivial | omega
    cases hs : e.side
    · exact Or.inr (.hit (by simpa [depthDirection, hs] using ha') hf)
    · exact Or.inl (.hit (by simpa [depthDirection, hs] using ha') hf)
  · let near := wallCell p e.side q.1 1 (by omega)
    have hc : q.1 ∉ l.pageColumnSet p e.side := fun hc => hx (g.columns _ hc hq.2)
    have hoff : near ∉ (l.twoPageStreets p hl).support := by
      intro hp
      rcases (l.page_support_iff_side p hl e.side near (wallCell_side p e.side q.1 1 (by omega))).mp hp with hr | hc'
      · exact wallCell_one_not_row l p e g q.1 hr
      · exact hc hc'
    have hn := off_page_blocker l p hl hoff
    have ha' : Adjacent (depthDirection e.side).opposite q near := by
      cases hs : e.side <;> simp only [depthDirection, wallCell, near, Direction.opposite, Adjacent, hs,
        reduceCtorEq, ite_true, ite_false] at hrow ⊢ <;> constructor <;> first | trivial | omega
    cases hs : e.side
    · exact Or.inl (.hit (by simpa [depthDirection, hs, Direction.opposite] using ha') hn)
    · exact Or.inr (.hit (by simpa [depthDirection, hs, Direction.opposite] using ha') hn)

/-- Every last-level inward r-wall component has an already proved blocked end on each axis. -/
theorem endpointRWall_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (e : Endpoint) (he : e ∈ l.endpoints) (g : EndpointWideSeparator l p e) (heM : e.level = p.levels) :
    Freeze.Anchored (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) := by
  intro d q hq
  obtain ⟨_, hw, hq⟩ := (mem_endpointRWall l p e g q).mp hq
  have hv : Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .north q ∨
      Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .south q := by
    rcases hq with hcap | hrow
    · have hr := r_one_vertical_ray l p hl hM ha e he g heM q hcap.1 hcap.2
      cases hs : e.side
      · exact Or.inr (by simpa [depthDirection, hs] using hr)
      · exact Or.inl (by simpa [depthDirection, hs] using hr)
    · exact r_row_vertical_ray l p hl hM ha e he g heM q hrow
  have hh : Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .east q ∨
      Freeze.Ray (l.endpointRWall p e g) (l.pageFrozenBlockers p hl) .west q := by
    rcases hq with hcap | hrow
    · obtain ⟨r, ha, hr⟩ := r_one_west_blocker l p hl e he g q hcap.1 hcap.2
      exact Or.inr (.hit ha hr)
    · have hneq : q.1.val ≠ g.cell.1.val := by
        intro hx
        have heq : q = g.cell := Prod.ext (Fin.ext hx) hrow.1
        exact hw (heq.symm ▸ g.hole)
      have hb := hrow.2
      cases hs : e.inward
      · simp only [hs, Bool.false_eq_true, ite_false] at hb
        exact Or.inr (west_r_wall_ray l p hl e g hs q hrow (by omega))
      · simp only [hs, ite_true] at hb
        exact Or.inl (east_r_wall_ray l p hl e g hs q hrow (by omega))
  cases d with
  | north => exact hv
  | south => exact hv.symm
  | east => exact hh
  | west => exact hh.symm

/-- The computed last-level r-wall extends the actual page closure. -/
theorem endpointRWall_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (g : EndpointWideSeparator l p e) (heM : e.level = p.levels) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g) :=
  .add (l.pageBackground_closure p hl hM ha initial target)
    (l.endpointRWall_initial_full p hl hM ha initial target e he g heM)
    (l.endpointRWall_anchored p hl hM ha e he g heM)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) (g : EndpointWideSeparator l p e) (heM : e.level = p.levels)

include he heM

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every successful physical trajectory avoids the actual last-level r-wall in every push. -/
theorem physicalInstance_endpoint_rwall_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none
      (I).initial u)
    (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (I).board none
      (l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g))
      (I).initial u :=
  (l.endpointRWall_closure p hl hM ha initial target e he g heM).reachable
    (l.physicalInstance_page_avoiding_prefix p hl hM ha initial target hsu hut ht)

/-- Actual initial box identities in the last-level r-wall stay at their original cells. -/
theorem physicalInstance_endpoint_rwall_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (I).initial)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none
      (I).initial u)
    (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    ∃ U : LabelledState ι (p.W + 1) (p.H + 1), U.state = u ∧
      Labels.GuardedReachable (I).board none
        (l.pageFrozenBlockers p hl ∪ l.endpointRWall p e g) S U ∧
      ∀ i, S.position i ∈ l.endpointRWall p e g → U.position i = S.position i := by
  have hguard := l.physicalInstance_endpoint_rwall_avoiding p hl hM ha initial target
    e he g heM hsu hut ht
  rw [← hS] at hguard
  obtain ⟨U, hU, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨U, hU, hlabels, fun i hi => hlabels.position i (Finset.mem_union_right _ hi)⟩

end Solution
end PushPuzzle.PushS.PortLayout

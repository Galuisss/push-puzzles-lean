/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortWideGeometry
import Mathlib.Data.Finset.Max
import all PushS.PortWideGeometry
import all PushS.PortTwoPageStreets
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortCentralMargins
import all PushS.PortStreetEnumeration
import all PushS.PortSegmentBounds
import all PushS.PortEndpointCounts
import all PushS.PortWireIndexing
import all PushS.PortWireGeometry
import all PushS.PortEndpointCrossing
import all PushS.PortLayoutCoordinates
import all PushS.PortAxisClear
import all PushS.PortFixedSeparation
import all PushS.PortSegments

/-!
# Actual inward wide separators at ordinary endpoints

The nearest page column beyond an ordinary endpoint's inward auxiliary column is separated
by a wide gap. The last branch row and the selected rows shallower than the endpoint have
no group crossing that gap. The emitted separator stays inside it after even rounding.
-/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- An actual selected-row wide separator beyond an endpoint's inward street, with no
intervening page column other than that street. -/
structure EndpointWideSeparator (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (v : ℕ := p.Y p.levels + 2) where
  /-- Actual finite emitted cell. -/
  cell : Cell (p.W + 1) (p.H + 1)
  /-- Membership after the emitter's conditional rounding. -/
  hole : cell ∈ l.wideSeparatorHoles p
  /-- The selected depth, reflected on the lower page. -/
  row : cell.2.val = if e.side = .upper then v else p.H - v
  /-- The separator is strictly beyond the inward auxiliary street. -/
  forward : if e.inward then p.x e.port + 2 < cell.1.val else cell.1.val < p.x e.port - 2
  /-- That street is the only page column between the axis and the separator. -/
  columns : ∀ z ∈ l.pageColumnCoordinates p e.side,
    (if e.inward then p.x e.port < z ∧ z ≤ cell.1.val else cell.1.val ≤ z ∧ z < p.x e.port) →
      z = if e.inward then p.x e.port + 2 else p.x e.port - 2

private theorem nearby_axis_eq (p : Scales.Parameters) {i k z : ℕ}
    (hz : Nat.dist z (p.x i) ≤ p.L p.levels + 16)
    (hk : p.x k - (p.L p.levels + 12) ≤ z ∧ z ≤ p.x k + p.L p.levels + 12) : k = i := by
  have hD := p.outer_distance
  by_contra hne
  rcases lt_or_gt_of_ne hne with h | h
  all_goals have hs := axis_spacing p h
  all_goals simp only [Nat.dist] at hz; omega

private theorem nearby_page_columns (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {z : ℕ} (hz : z ∈ l.pageColumnCoordinates p e.side)
    (hnear : Nat.dist z (p.x e.port) ≤ p.L p.levels + 12) :
    z = p.x e.port ∨ z = (auxiliary (coordinates p) e).1 ∨
      z = (auxiliary (coordinates p) e).2 := by
  have hm := readLength_add_lt_x p e.port p.levels
  have hW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hm hW
  have hL := length_floor p
  change z ∈ pageColumns l (coordinates p) e.side at hz
  simp only [pageColumns, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hz
  change z = 0 ∨ z = p.W ∨ _ at hz
  rcases hz with rfl | rfl | hz | hz
  · simp only [Nat.dist] at hnear
    omega
  · simp only [Nat.dist] at hnear
    omega
  · obtain ⟨f, hf, hz⟩ := List.mem_flatMap.mp hz
    obtain ⟨hf, hside⟩ := List.mem_filter.mp hf
    have hside : f.side = e.side := of_decide_eq_true hside
    have hp := nearby_axis_eq p (i := e.port) (by omega) (endpoint_columns_span p f hz)
    have hfe := l.endpoints_key_injective hl hf he hside hp
    subst f
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hz
    tauto
  · split at hz
    · rename_i hs
      obtain ⟨i, hi, hz⟩ := List.mem_flatMap.mp hz
      have hp := nearby_axis_eq p (i := e.port) (by omega) (center_columns_span p i hz)
      obtain ⟨kind, first, hg, hi⟩ := center_gate_mem l hi
      exact False.elim (l.endpoints_lower_ne_gate_middle hl hg he hs (by omega))
    · cases hz

private theorem nearby_inward_column (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {z : ℕ} (hz : z ∈ l.pageColumnCoordinates p e.side)
    (hnear : Nat.dist z (p.x e.port) ≤ p.L p.levels + 12)
    (hdir : if e.inward then p.x e.port < z else z < p.x e.port) :
    z = if e.inward then p.x e.port + 2 else p.x e.port - 2 := by
  have hc : (coordinates p).x e.port = p.x e.port := rfl
  rcases nearby_page_columns l p hl ha he hz hnear with hz | hz | hz
  all_goals cases hd : e.inward <;>
    simp only [auxiliary, inward, outward, hd, Bool.false_eq_true, ite_true, ite_false, hc] at hz hdir ⊢ <;>
    omega

private theorem adjacent_pair_of_gap {xs : List ℕ} {a b : ℕ}
    (ha : a ∈ xs) (hb : b ∈ xs) (hab : a < b)
    (hgap : ∀ z ∈ xs, ¬(a < z ∧ z < b)) : (a, b) ∈ adjacentPairs xs := by
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, List.mem_filterMap.mpr ⟨b, hb, ?_⟩⟩
  have hno : xs.any (fun z => decide (a < z ∧ z < b)) = false := by
    apply Bool.eq_false_iff.mpr
    intro h
    obtain ⟨z, hz, hmid⟩ := List.any_eq_true.mp h
    exact hgap z hz (of_decide_eq_true hmid)
  exact ite_eq_left ⟨hab, by rw [hno]; rfl⟩

private theorem next_column (xs : List ℕ) {a : ℕ} (ha : a ∈ xs)
    (hex : ∃ b ∈ xs, a < b) : ∃ b, (a, b) ∈ adjacentPairs xs := by
  have hb := Nat.find_spec hex
  refine ⟨Nat.find hex, adjacent_pair_of_gap ha hb.1 hb.2 ?_⟩
  intro z hz hmid
  have := Nat.find_min' hex ⟨hz, hmid.1⟩
  omega

private theorem previous_column (xs : List ℕ) {b : ℕ} (hb : b ∈ xs)
    (hex : ∃ a ∈ xs, a < b) : ∃ a, (a, b) ∈ adjacentPairs xs := by
  let earlier := xs.toFinset.filter fun a => a < b
  have hne : earlier.Nonempty := by
    obtain ⟨a, ha, hab⟩ := hex
    exact ⟨a, Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr ha, hab⟩⟩
  have hm := Finset.mem_filter.mp (Finset.max'_mem earlier hne)
  refine ⟨earlier.max' hne, adjacent_pair_of_gap (List.mem_toFinset.mp hm.1) hb hm.2 ?_⟩
  intro z hz hmid
  have := Finset.le_max' earlier z (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hz, hmid.2⟩)
  omega

private theorem inward_gap (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints) :
    ∃ a b, (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p e.side) ∧
      p.L p.levels < b - a ∧
      (if e.inward then a = p.x e.port + 2 else b = p.x e.port - 2) := by
  have hc : (coordinates p).x e.port = p.x e.port := rfl
  have hr : (auxiliary (coordinates p) e).2 ∈ l.pageColumnCoordinates p e.side :=
    endpoint_columns_mem l p e he (by simp)
  have hL := readLength_add_lt_x p e.port p.levels
  have hR := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hL hR
  cases hd : e.inward with
  | false =>
    simp only [auxiliary, inward, hd, Bool.false_eq_true, ite_false, hc] at hr
    have hzero : 0 ∈ l.pageColumnCoordinates p e.side := by simp [pageColumnCoordinates, pageColumns]
    obtain ⟨a, hab⟩ := previous_column _ hr ⟨0, hzero, by omega⟩
    have hgap := (adjacentPair_gap hab).1
    have ha' := (adjacentPair_mem hab).1
    have hwide : p.L p.levels < p.x e.port - 2 - a := by
      by_contra h
      have hnear : Nat.dist a (p.x e.port) ≤ p.L p.levels + 12 := by
        simp only [Nat.dist]
        omega
      have heq := nearby_inward_column l p hl ha he ha' hnear
        (by simp only [hd, Bool.false_eq_true, ite_false]; omega)
      simp only [hd, Bool.false_eq_true, ite_false] at heq
      omega
    exact ⟨a, p.x e.port - 2, hab, hwide, by simp⟩
  | true =>
    simp only [auxiliary, inward, hd, ite_true, hc] at hr
    have hframe : p.W ∈ l.pageColumnCoordinates p e.side := by
      simp [pageColumnCoordinates, pageColumns, show (coordinates p).W = p.W from rfl]
    obtain ⟨b, hab⟩ := next_column _ hr ⟨p.W, hframe, by omega⟩
    have hgap := (adjacentPair_gap hab).1
    have hb := (adjacentPair_mem hab).2
    have hwide : p.L p.levels < b - (p.x e.port + 2) := by
      by_contra h
      have hnear : Nat.dist b (p.x e.port) ≤ p.L p.levels + 12 := by
        simp only [Nat.dist]
        omega
      have heq := nearby_inward_column l p hl ha he hb hnear
        (by simp only [hd, ite_true]; omega)
      simp only [hd, ite_true] at heq
      omega
    exact ⟨p.x e.port + 2, b, hab, hwide, by simp⟩

private theorem last_row_uncrossed (l : PortLayout) (p : Scales.Parameters)
    (side : Side) (a b : ℕ) :
    crosses l (coordinates p) side a b (p.Y p.levels + 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨g, _, hg⟩ := List.any_eq_true.mp h
  have he := (of_decide_eq_true hg).2.1
  have hb := readDepth_le_last p g.level
  change readDepth p g.level = p.Y p.levels + 2 at he
  omega

private theorem wide_point_of_uncrossed (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {a b v : ℕ} (hab : (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p side))
    (hwide : p.L p.levels < b - a) (hv : v ∈ l.workingDepthCoordinates p)
    (hcross : crosses l (coordinates p) side a b v = false) :
    point ((a + b) / 2) (onSide (coordinates p) side v) ∈ wideFixed l (coordinates p) side := by
  apply List.mem_flatMap.mpr
  refine ⟨(a, b), hab, ?_⟩
  have hlength : (coordinates p).length (coordinates p).levels < b - a := by
    change readLength p p.levels < b - a
    rwa [readLength_eq p p.levels_pos le_rfl]
  dsimp only
  rw [ite_eq_left hlength]
  apply List.mem_filterMap.mpr
  refine ⟨v, hv, ?_⟩
  rw [hcross]
  rfl

private theorem shifted_point (guards rows : List ℕ) (x y : ℕ) :
    ∃ u, u ≤ x ∧ x ≤ u + 1 ∧ shiftPoint guards rows (point x y) = point u y := by
  unfold shiftPoint
  split
  · have hm := Nat.mod_lt x (by decide : 0 < 2)
    exact ⟨x - x % 2, by omega, by omega, by simp [point, segment]⟩
  · exact ⟨x, le_rfl, by omega, rfl⟩

private theorem rounded_wide_point (l : PortLayout) (p : Scales.Parameters) (side : Side)
    (x y : ℕ) (hp : point x y ∈ wideFixed l (coordinates p) side) :
    ∃ u, u ≤ x ∧ x ≤ u + 1 ∧ point u y ∈ physicalWideSegments l p side := by
  dsimp only [physicalWideSegments]
  split
  · obtain ⟨u, hu, hu', he⟩ := shifted_point _ _ x y
    exact ⟨u, hu, hu', List.mem_map.mpr ⟨_, hp, he⟩⟩
  · exact ⟨x, le_rfl, by omega, hp⟩

private theorem wide_cell_of_uncrossed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side)
    {a b v : ℕ} (hv : v ∈ l.workingDepthCoordinates p)
    (hab : (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p side))
    (hwide : p.L p.levels < b - a)
    (hcross : crosses l (coordinates p) side a b v = false) :
    ∃ g : Cell (p.W + 1) (p.H + 1), g ∈ l.wideSeparatorHoles p ∧
      g.2.val = (if side = .upper then v else p.H - v) ∧ a < g.1.val ∧ g.1.val < b := by
  obtain ⟨x, hx, hx', hp⟩ := rounded_wide_point l p side _ _
    (wide_point_of_uncrossed l p side hab hwide hv hcross)
  have hg := (adjacentPair_gap hab).1
  have hL := length_floor p
  have hinside : a < x ∧ x < b := by omega
  have hb := pageColumn_le l p hl ha side (adjacentPair_mem hab).2
  have hy : onSide (coordinates p) side v ≤ p.H :=
    onSide_le p side (Nat.le_of_lt (workingDepth_positive l p hv).2)
  let g : Cell (p.W + 1) (p.H + 1) :=
    (⟨x, by omega⟩, ⟨onSide (coordinates p) side v, by omega⟩)
  refine ⟨g, ?_, rfl, hinside⟩
  apply (SegmentRecipe.mem_holes _ g).mpr
  refine ⟨point x (onSide (coordinates p) side v), ?_, ?_⟩
  · cases hs : side with
      | upper => exact List.mem_append_left _ (hs ▸ hp)
      | lower => exact List.mem_append_right _ (hs ▸ hp)
  · simp [g, point, segment, Segment.Contains]

private theorem inward_separator_of_gap (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {a b v : ℕ} (hv : v ∈ l.workingDepthCoordinates p)
    (hab : (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p e.side))
    (hwide : p.L p.levels < b - a)
    (hdir : if e.inward then a = p.x e.port + 2 else b = p.x e.port - 2)
    (hcross : crosses l (coordinates p) e.side a b v = false) :
    Nonempty (EndpointWideSeparator l p e v) := by
  obtain ⟨g, hhole, hrow, hinside⟩ := wide_cell_of_uncrossed l p hl ha e.side hv hab hwide hcross
  refine ⟨⟨g, hhole, hrow, ?_, ?_⟩⟩
  · cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hdir ⊢ <;> omega
  · intro z hz hzin
    have hno := (adjacentPair_gap hab).2 z hz
    have hnear : Nat.dist z (p.x e.port) ≤ p.L p.levels + 12 := by
      cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hdir hzin <;>
        simp only [Nat.dist] <;> omega
    apply nearby_inward_column l p hl ha he hz hnear
    cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hzin ⊢
    · exact hzin.2
    · exact hzin.1

/-- Every actual ordinary endpoint has an emitted wide separator in its inward direction
on the last allocated branch row. -/
theorem endpointWideSeparator_nonempty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints) :
    Nonempty (EndpointWideSeparator l p e) := by
  obtain ⟨a, b, hab, hwide, hdir⟩ := inward_gap l p hl ha he
  apply inward_separator_of_gap l p hl ha he ?_ hab hwide hdir (last_row_uncrossed l p e.side a b)
  have hj : p.levels - 1 + 1 = p.levels := by have := p.levels_pos; omega
  have hy := (l.workingDepthCoordinates_mem p (p.levels - 1) (by have := p.levels_pos; omega)).2
  rwa [hj, readDepth_eq p p.levels_pos le_rfl] at hy

private theorem inward_span_level (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {e : Endpoint} (he : e ∈ l.endpoints) {g : Placement} (hg : g ∈ placements l)
    (hs : e.side = g.side)
    (hspan : p.x g.left ≤ (auxiliary (coordinates p) e).2 ∧
      (auxiliary (coordinates p) e).2 ≤ p.x g.right) : e.level ≤ g.level := by
  have hr : p.x e.port - 2 ≤ (auxiliary (coordinates p) e).2 ∧
      (auxiliary (coordinates p) e).2 ≤ p.x e.port + 2 := by
    have hc : (coordinates p).x e.port = p.x e.port := rfl
    cases hi : e.inward <;> simp [auxiliary, inward, hc, hi] <;> omega
  have hD := readDepth_add_lt_D p 0
  have hports : g.left ≤ e.port ∧ e.port ≤ g.right := by
    constructor
    · by_contra! h
      have := axis_spacing p h
      omega
    · by_contra! h
      have := axis_spacing p h
      omega
  by_cases hleft : e.port = g.left
  · have heq := l.endpoints_key_injective hl he (placement_endpoints l hg).1 hs hleft
    exact Nat.le_of_eq (congrArg Endpoint.level heq)
  by_cases hright : e.port = g.right
  · have heq := l.endpoints_key_injective hl he (placement_endpoints l hg).2 hs hright
    exact Nat.le_of_eq (congrArg Endpoint.level heq)
  have hinside : g.left < e.port ∧ e.port < g.right := by omega
  cases hk : g.gate with
  | none => exact Nat.le_of_lt (interior_endpoint_shallower l hl hg hk he hs hinside.1 hinside.2)
  | some kind =>
    have hshape := placement_gate_shape l hg hk
    exact False.elim (l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he
      (hs.trans hshape.1) (by omega))

private theorem inward_gap_uncrossed_before (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    {a b v : ℕ} (hab : (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p e.side))
    (hin : if e.inward then a = p.x e.port + 2 else b = p.x e.port - 2)
    (hv : v < readDepth p e.level) : crosses l (coordinates p) e.side a b v = false := by
  apply Bool.eq_false_iff.mpr
  intro hcross
  obtain ⟨g, hg, hcross⟩ := List.any_eq_true.mp hcross
  obtain ⟨hside, hrow, hleft, _, hright⟩ := of_decide_eq_true hcross
  have hgap := (adjacentPair_gap hab).1
  have hc : (coordinates p).x = p.x := rfl
  have hspan : p.x g.left ≤ (auxiliary (coordinates p) e).2 ∧
      (auxiliary (coordinates p) e).2 ≤ p.x g.right := by
    simp only [hc] at hleft hright
    cases hi : e.inward <;>
      simp only [auxiliary, inward, hi, Bool.false_eq_true, ite_true, ite_false, hc] at hin ⊢ <;> omega
  have hlevel := inward_span_level l p hl he hg hside.symm hspan
  have heLevel := l.endpoints_level_bounds p hl hM he
  have hgLevel := placement_level_bounds l hl hg
  have hmono : readDepth p e.level ≤ readDepth p g.level := by
    rw [readDepth_eq p heLevel.1 heLevel.2,
      readDepth_eq p hgLevel.1 (hgLevel.2.trans hM)]
    exact Y_le p hlevel
  change readDepth p g.level = v at hrow
  omega

/-- Every selected row shallower than an actual ordinary endpoint has a real inward wide
separator beyond its r street. -/
theorem endpointWideSeparator_before_nonempty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {v : ℕ} (hv : v ∈ l.workingDepthCoordinates p)
    (hve : v < readDepth p e.level) : Nonempty (EndpointWideSeparator l p e v) := by
  obtain ⟨a, b, hab, hwide, hin⟩ := inward_gap l p hl ha he
  exact inward_separator_of_gap l p hl ha he hv hab hwide hin
    (inward_gap_uncrossed_before l p hl hM he hab hin hve)

private theorem endpoint_branch_row_uncrossed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints)
    (side : Side) (a b : ℕ) :
    crosses l (coordinates p) side a b (readDepth p e.level + 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro hcross
  obtain ⟨g, hg, hcross⟩ := List.any_eq_true.mp hcross
  have hrow := (of_decide_eq_true hcross).2.1
  change readDepth p g.level = readDepth p e.level + 2 at hrow
  have heLevel := l.endpoints_level_bounds p hl hM he
  have hgLevel := placement_level_bounds l hl hg
  rcases lt_trichotomy e.level g.level with h | h | h
  · have hgap := depth_gap p heLevel.1 h (hgLevel.2.trans hM)
    omega
  · have heq := congrArg (readDepth p) h
    omega
  · have hgap := depth_gap p hgLevel.1 h heLevel.2
    omega

private theorem endpoint_branch_depth_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint} (he : e ∈ l.endpoints) :
    readDepth p e.level + 2 ∈ l.workingDepthCoordinates p := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hi : e.level - 1 + 1 = e.level := by omega
  have hv := (l.workingDepthCoordinates_mem p (e.level - 1) (by omega)).2
  rwa [hi] at hv

/-- Every ordinary endpoint has an actual inward wide separator on its own branch row,
two cells deeper than its work row. -/
theorem endpointWideSeparator_after_nonempty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) :
    Nonempty (EndpointWideSeparator l p e (readDepth p e.level + 2)) := by
  obtain ⟨a, b, hab, hwide, hin⟩ := inward_gap l p hl ha he
  exact inward_separator_of_gap l p hl ha he (endpoint_branch_depth_mem l p hl hM he) hab hwide hin
    (endpoint_branch_row_uncrossed l p hl hM he e.side a b)

private theorem inward_interval_far_axes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) {v x : ℕ} (g : EndpointWideSeparator l p e v)
    (hbetween : if e.inward then p.x e.port < x ∧ x ≤ g.cell.1.val
      else g.cell.1.val ≤ x ∧ x < p.x e.port)
    (hfar : p.L p.levels + 16 < Nat.dist x (p.x e.port)) :
    ∀ i < l.portCount, p.L p.levels + 12 < Nat.dist x (p.x i) := by
  intro i hi
  have hm := x_add_readLength_lt_W p (show i < p.axes by omega) 0
  let col : Fin (p.W + 1) := ⟨p.x i, by omega⟩
  have hcol : col ∈ l.streetColumnSet p := axis_in_streetColumns l p hi
  have hwide := l.wideSeparatorHoles_street_gap p hl g.hole col hcol
  have hb := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
    (show 1 ≤ 8 * (p.axes + 1) by omega)
  simp only [Nat.one_mul] at hb
  have hbudget : p.L p.levels + 16 < 2 * p.b p.levels + 2 := by
    unfold Scales.Parameters.b
    omega
  have hnr : (if e.inward then p.x e.port + 2 else p.x e.port - 2) ≠ p.x i := by
    exact auxiliary_off_axis l p hl hM he i (Or.inr rfl)
  have hno : ¬(if e.inward then p.x e.port < p.x i ∧ p.x i ≤ g.cell.1.val
      else g.cell.1.val ≤ p.x i ∧ p.x i < p.x e.port) := by
    intro h
    exact hnr (g.columns _ (axis_in_pageColumns l p hl e.side hi) h).symm
  cases hd : e.inward <;>
    simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hno hbetween <;>
    simp only [Nat.dist, col] at hfar hwide ⊢ <;> omega

private theorem inward_interval_off_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {e : Endpoint} (he : e ∈ l.endpoints)
    {v : ℕ} (g : EndpointWideSeparator l p e v) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2 = g.cell.2)
    (hbetween : if e.inward then p.x e.port < q.1.val ∧ q.1.val ≤ g.cell.1.val
      else g.cell.1.val ≤ q.1.val ∧ q.1.val < p.x e.port) : q ∉ Boundary.frame := by
  have hgf := l.wideSeparatorHoles_off_frame p hl g.hole
  have hx0 := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) 0
  have hr := congrArg Fin.val hy
  have hgx := g.cell.1.isLt
  have hqx := q.1.isLt
  cases hd : e.inward <;> simp only [hd, Bool.false_eq_true, ite_true, ite_false] at hbetween
  all_goals
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hgf ⊢
    omega

end PushPuzzle.PushS.PortLayout

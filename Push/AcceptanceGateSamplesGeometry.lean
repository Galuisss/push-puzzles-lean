/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateWalks
public import PushS.PortDepthBands
import all PushS.PortGateMarkers
import all PushS.PortGatePublicWalk
import all PushS.PortGatePrivateWalk
import all PushS.PortGatePrivateEntry
import all PushS.PortGateBottomWall
import all PushS.PortGatePageWindow
import all PushS.PortInterlevelFreeze
import all PushS.PortEndpointLocality
import all PushS.PortCoreCrossing
import all PushS.PortBackground
import all PushS.PortCentralStrip
import all PushS.PortSegments
import all Push.AcceptanceSoundnessCentral

/-! A lower gate sample column has no deep work-row stock supplied by another source component. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe

private theorem gate_deep_near_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (haxes : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : p.x middle - 2 ≤ q.1.val ∧ q.1.val ≤ p.x middle + 12)
    (hy : p.D + 32 < q.2.val ∧ q.2.val < p.H) (hdepth : p.b 1 < p.H - q.2.val) :
    ∀ a ∈ l.deeperWalkHoles p 1, p.b 1 < distance a q := by
  obtain ⟨kind, first, hg, hcenter⟩ := center_gate_mem l hi
  have ho := budget_outer p p.levels_pos
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  dsimp only [columnRadius] at ho
  have hleft : p.D ≤ p.x middle := by
    simpa only [Nat.one_mul, Scales.Parameters.x] using
      Nat.mul_le_mul_right p.D (show 1 ≤ middle + 1 by omega)
  have hright : p.x middle + p.D ≤ p.W := by
    have hm := axis_spacing p ((gate_center_lt l hl hi).trans_le haxes)
    simpa only [Scales.Parameters.x, Scales.Parameters.W] using hm
  intro a ha
  rcases Finset.mem_union.mp ha with hf | hw
  · obtain ⟨d, hb⟩ := (Boundary.mem_frame a).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hb <;>
      simp only [distance, Nat.dist_eq_max_sub_min] <;> omega
  obtain ⟨s, hs, hac⟩ := (SegmentRecipe.mem_holes _ a).mp hw
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  have he := (List.mem_filter.mp he).1
  have hae : (a.1.val, a.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e) :=
    (mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_take hs, hac⟩
  have hes := fixed_endpoint_span l p e hae
  have hL := readLength_le_last p e.level
  by_cases hp : e.port = middle
  · have hside : e.side = .upper := by
      cases hs : e.side
      · rfl
      · exact False.elim (l.endpoints_lower_ne_gate_middle hl hg he hs (hp.trans hcenter))
    have hb := endpoint_page_band l p e hae
    simp only [hside, ite_true] at hb
    simp only [distance, Nat.dist_eq_max_sub_min]
    omega
  · rcases lt_or_gt_of_ne hp with hlt | hgt
    · have hgap := axis_spacing p hlt
      simp only [distance, Nat.dist_eq_max_sub_min]
      omega
    · have hgap := axis_spacing p hgt
      simp only [distance, Nat.dist_eq_max_sub_min]
      omega

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushFS.Reduction PushS PushS.PortLayout AcceptanceProgram SegmentRecipe

/-- A real accepted lower sample column has no holes in the deeper work bands. -/
private theorem canonical_gate_sample_deep_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 2 ∨ q.1.val = p.x middle + 10)
    (hy : p.D + 32 < q.2.val ∧ q.2.val < p.H) (hdepth : p.b 1 < p.H - q.2.val) : q ∈ t.boxes := by
  have hpos := readDepth_ge p le_rfl p.levels_pos
  have hb : readDepth p 1 + 2 < p.b 1 := by
    rw [readDepth_eq p le_rfl p.levels_pos]
    have hm := Nat.mul_le_mul_right (p.Y 1 + p.L 1 + 10) (show 1 ≤ 8 * (p.axes + 1) by omega)
    simp only [Nat.one_mul] at hm
    unfold Scales.Parameters.b
    omega
  have hfar := gate_deep_near_far l p hl haxes hi (q := q) (by omega) hy hdepth
  have before := canonical_deeper_preserving l p hl hM haxes initial target hgate 1
    (u := (l.canonicalInstance p hl hM haxes initial target).initial) .refl hr accepted
  have after := canonical_deeper_preserving l p hl hM haxes initial target hgate 1 hr .refl accepted
  have hempty := canonical_deeperWalk_empty l p hl hM haxes initial target hgate 1 .refl hr accepted
  have hplayer : (l.canonicalInstance p hl hM haxes initial target).initial.player ∈ l.deeperWalkHoles p 1 :=
    Finset.mem_union_left _ (canonical_initial_frame l p hl hM haxes initial target)
  have hbudget := l.encodedSegments_outside_deeperWalk_card_le p hl hM haxes (l.canonical initial) le_rfl
  change (targetHoles l p initial \ l.deeperWalkHoles p 1).card ≤ p.b 1 at hbudget
  rw [← canonical_initial_holes l p hl hM haxes initial target] at hbudget
  by_contra hbox
  have hhole : q ∈ holes t := (PushS.mem_holes _).mpr hbox
  have hsource := Radius.distant_hole_at before after hempty hplayer
    (fun a ha => hbudget.trans_lt (hfar a ha)) hhole
  have henc : q ∈ targetHoles l p initial := by
    rw [← canonical_initial_holes l p hl hM haxes initial target]
    exact hsource
  have hw : q ∈ gatePageWindow p middle := ⟨hy, by simp only [Nat.dist]; omega⟩
  have hs := l.encodedSegments_gatePageWindow p hl hM haxes (l.canonical initial) hi hw henc
  cases hs with
  | fixed hf =>
    cases gateFixedSegments_location p middle hf with
    | publicStreet hc _ =>
      simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
      omega
    | privateCap _ hy => omega
    | privateBranch hy _ => omega
    | halfDepth hy => omega
    | marker _ hc _ =>
      change q.1.val ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      have hx0 := readLength_add_lt_x p middle 0
      omega
  | @signal kind first internal _ hm hs =>
    cases gateSegments_location p (l.canonical initial) kind first internal hs with
    | horizontal hy => omega
    | axis hc _ =>
      change q.1.val = p.x (first + 1) at hc
      rw [hm] at hc
      omega

/-- The bottom bar below the right independent sample stays occupied on the real path. -/
private theorem canonical_gate_ten_branch_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 10) (hy : q.2.val = p.H - (readDepth p 1 + 2)) : q ∈ t.boxes := by
  classical
  let left := gateLeftSeparator l p hl hM haxes hi
  let right := gateRightSeparator l p hl hM haxes hi
  have hleft := left.outside
  have hright := right.outside
  simp only [Bool.false_eq_true, ite_false, ite_true] at hleft hright
  have hY := readDepth_ge p le_rfl p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hw : q ∈ gatePageWindow p middle := ⟨⟨by omega, by omega⟩, by simp only [Nat.dist]; omega⟩
  have hwall : q ∈ l.gateBottomWall p middle left right := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, gate_window_not_wide l p hl haxes hi hw, Or.inr ?_⟩
    · intro hc
      have hb := (Finset.mem_filter.mp hc).2
      omega
    · exact ⟨hy, Or.inr ⟨by omega, by omega⟩⟩
  have hblock : q ∈ l.gatePrivateBlockers p hl hM haxes hi :=
    Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hwall))
  exact avoiding_box (canonical_gate_private_avoiding_prefix l p hl hM haxes initial target hgate hi hr .refl accepted)
    hblock (l.gateBottomWall_initial_full p hl hM haxes (l.canonical initial) (l.canonical target) hi left right hwall)

/-- On either independent sample column, lower terminal holes lie on the gate work row or its real left private branch. -/
theorem canonical_gate_sample_lower_location (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (initial target : List Bool) (hgate : l.gateCenterCoordinates ≠ [])
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (accepted : Scan.Accepts (instructions (program l p target).rounds) (holes t))
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 2 ∨ q.1.val = p.x middle + 10)
    (hy : p.D + 4 < q.2.val) (hf : q ∉ Boundary.frame) (hq : q ∈ holes t) :
    q.2.val = p.H - readDepth p 1 ∨
      (q.1.val = p.x middle + 2 ∧ q.2.val = p.H - (readDepth p 1 + 2)) := by
  have hD := p.outer_distance
  have hH : p.H = 2 * p.D := rfl
  have hnotcentral : q ∉ l.centralMarkers p := fun h => by have hb := (Finset.mem_filter.mp h).2; omega
  have hfill : q ∉ (Blocked.fill t (l.centralMarkers p)).boxes := by
    intro hb
    exact (Finset.mem_union.mp hb).elim ((PushS.mem_holes _).mp hq) hnotcentral
  have hsupp := canonical_pages_supported_at l p hl hM haxes initial target hr .refl accepted q hfill
  have hworking : q.2 ∈ l.workingRowSet p := by
    rcases (l.page_support_iff_side p hl .lower q (by simp only [reduceCtorEq, ite_false]; omega)).mp hsupp with hw | hc
    · exact hw
    · have hcol := l.gatePageColumns_near p hl haxes hi hc (by simp only [Nat.dist]; omega)
      have hx0 := readLength_add_lt_x p middle 0
      change q.1.val ∈ [p.x middle, p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hcol
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol
      omega
  have hqH : q.2.val < p.H := by
    have hqbound := q.2.isLt
    by_contra hn
    exact hf ((Boundary.mem_frame q).mpr ⟨.south, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩)
  rcases (l.workingRowSet_iff p q.2).mp hworking with h0 | hH' | ⟨v, hv, hrow⟩
  · omega
  · omega
  have hvlast := workingRows_le_last l p hv
  have hlast := last_depth_margin p
  have hrow : q.2.val = p.H - v := hrow.resolve_left (by omega)
  have hvmin := l.workingDepthCoordinates_gate_min p hi hv
  rcases l.workingDepthCoordinates_bands p le_rfl p.levels_pos hv with hshallow | hbranch | ⟨hlevels, hdeep⟩
  · exact Or.inl (by omega)
  · have hqy : q.2.val = p.H - (readDepth p 1 + 2) := by omega
    rcases hx with htwo | hten
    · exact Or.inr ⟨htwo, hqy⟩
    · exact False.elim ((PushS.mem_holes _).mp hq
        (canonical_gate_ten_branch_full l p hl hM haxes initial target hgate hr accepted hi hten hqy))
  · have hmid := middle_depth_bounds p le_rfl hlevels
    have hgap := l.workingRowSet_central_gap p hworking
    have hdeepbox := canonical_gate_sample_deep_full l p hl hM haxes initial target hgate hr accepted hi hx
      ⟨by omega, hqH⟩ (by omega)
    exact False.elim ((PushS.mem_holes _).mp hq hdeepbox)

end PushPuzzle.Push.AcceptanceSoundness

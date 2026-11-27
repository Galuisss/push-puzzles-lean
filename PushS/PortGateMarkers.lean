/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePageWindow
public import PushS.PortOrdinaryWalks
import all PushS.PortGatePageWindow
import all PushS.PortInterlevelFreeze
import all PushS.PortEndpointLocality
import all PushS.PortEndpointCrossing
import all PushS.PortCentralStrip
import all PushS.PortStreetEnumeration
import all PushS.PortPageBackground
import all PushS.PortBackground
import all PushS.PortSegments

/-! Actual interlevel anchors for the five special gate columns. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The emitted special-column holes between the first and second working levels. -/
noncomputable def gateInterlevelMarkers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => 1 < p.levels ∧ ∃ middle ∈ l.gateCenterCoordinates,
    q.1.val ∈ specialColumns (coordinates p) middle ∧
      q.2.val = p.H - (readDepth p 1 + readDepth p 2) / 2

private theorem gate_marker_data (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateInterlevelMarkers p) :
    1 < p.levels ∧ ∃ middle ∈ l.gateCenterCoordinates,
      q.1.val ∈ specialColumns (coordinates p) middle ∧
        q.2.val = p.H - (readDepth p 1 + readDepth p 2) / 2 := by
  classical
  simpa only [gateInterlevelMarkers, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem gate_special_span (p : Scales.Parameters) {middle x : ℕ}
    (hx : x ∈ specialColumns (coordinates p) middle) : p.x middle - 2 ≤ x ∧ x ≤ p.x middle + 12 := by
  change x ∈ [p.x middle - 2, p.x middle + 4, p.x middle + 6, p.x middle + 8, p.x middle + 12] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  omega

/-- Every special gate interlevel marker is a literal fixed hole of every actual encoding. -/
theorem gateInterlevelMarkers_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) : l.gateInterlevelMarkers p ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨hlevels, middle, hi, hx, hy⟩ := gate_marker_data l p hq
  let s := point q.1.val (p.H - (readDepth p 1 + readDepth p 2) / 2)
  have hs : s ∈ gateFixedSegments (coordinates p) middle := by
    simp only [gateFixedSegments, List.mem_append]
    apply Or.inr
    rw [ite_eq_left (show 1 < (coordinates p).levels from hlevels)]
    exact List.mem_map.mpr ⟨q.1.val, hx, rfl⟩
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.gateFixedSegments_mem_fixed p hi hs), ?_⟩
  simp only [s, point, segment, Segment.Contains, Nat.min_self, Nat.max_self, hy,
    le_refl, and_self, true_or]

private theorem gate_marker_frame_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) (hlevels : 1 < p.levels)
    {q a : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ specialColumns (coordinates p) middle)
    (hy : q.2.val = p.H - (readDepth p 1 + readDepth p 2) / 2)
    (hf : a ∈ Boundary.frame) : p.b 1 < distance a q := by
  have hs := gate_special_span p hx
  have ho := budget_outer p (show 1 ≤ p.levels by omega)
  have hd := middle_depth_bounds p (show 1 ≤ 1 by omega) hlevels
  simp only [Nat.reduceAdd] at hd
  have hleft : p.D ≤ p.x middle := by
    simpa only [Nat.one_mul, Scales.Parameters.x] using
      Nat.mul_le_mul_right p.D (show 1 ≤ middle + 1 by omega)
  have hright : p.x middle + p.D ≤ p.W := by
    have hm := axis_spacing p ((gate_center_lt l hl hi).trans_le ha)
    simpa only [Scales.Parameters.x, Scales.Parameters.W] using hm
  dsimp only [columnRadius] at ho
  obtain ⟨d, hb⟩ := (Boundary.mem_frame a).mp hf
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hb <;>
    simp only [distance, Nat.dist_eq_max_sub_min] <;> omega

/-- The actual special gate markers lie beyond the first-level residual budget from all
already cleared deeper ordinary public walks. -/
theorem gateInterlevelMarkers_far (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.gateInterlevelMarkers p) :
    ∀ a ∈ l.deeperWalkHoles p 1, p.b 1 < distance a q := by
  obtain ⟨hlevels, middle, hi, hx, hy⟩ := gate_marker_data l p hq
  obtain ⟨kind, first, hg, hcenter⟩ := center_gate_mem l hi
  have hqs := gate_special_span p hx
  have ho := budget_outer p (show 1 ≤ p.levels by omega)
  have hd := (middle_depth_bounds p (show 1 ≤ 1 by omega) hlevels).2.2
  simp only [Nat.reduceAdd] at hd
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  dsimp only [columnRadius] at ho
  intro a haP
  rcases Finset.mem_union.mp haP with hf | hw
  · exact gate_marker_frame_far l p hl ha hi hlevels hx hy hf
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

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Every actual successful play leaves the five special gate interlevel holes empty and unvisited. -/
theorem physicalInstance_gate_interlevel_excluded {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) : Blocked.Excluded (l.gateInterlevelMarkers p) u := by
  have hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.deeperWalkHoles p 1 ⊆ holes s :=
    fun _ hs hst => l.physicalInstance_deeperWalk_empty p hl hM ha initial target 1 hs hst ht
  have hsu' := deeper_preserving_between l p hl hM ha initial target 1 .refl hsu hut hP
  have hut' := deeper_preserving_between l p hl hM ha initial target 1 hsu hut .refl hP
  have hPi := hP _ .refl (hsu.trans hut)
  have hp : (I).initial.player ∈ l.deeperWalkHoles p 1 :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target)
  have hfar (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.gateInterlevelMarkers p) :
      ∀ a ∈ l.deeperWalkHoles p 1, (holes (I).initial \ l.deeperWalkHoles p 1).card < distance a q := by
    have hb := l.encodedSegments_outside_deeperWalk_card_le p hl hM ha initial (show 1 ≤ 1 by omega)
    rw [← l.physicalInstance_initial_holes p hl hM ha initial target] at hb
    exact fun a hap => hb.trans_lt (l.gateInterlevelMarkers_far p hl ha hq a hap)
  constructor
  · intro q hq
    have hfinal : q ∈ holes t := by
      change q ∈ t.boxesᶜ
      rw [ht]
      change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ
      rw [compl_compl]
      exact l.gateInterlevelMarkers_subset_encoded p target hq
    exact Radius.distant_hole_at hsu' hut' hPi hp (hfar q hq) hfinal
  · intro hq
    exact Radius.player_ne_distant hsu' hPi hp (hfar u.player hq) rfl

/-- Every actual successful prefix avoids the page blockers and all special gate markers. -/
theorem physicalInstance_gate_marker_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p)) (I).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  have hbt := hbu.trans hut
  exact (step_page_avoiding l p hl hM ha initial target hsa hm hbt ht).union_excluded
    (l.physicalInstance_gate_interlevel_excluded p hl hM ha initial target hsa
      ((Relation.ReflTransGen.single hm).trans hbt) ht)
    (l.physicalInstance_gate_interlevel_excluded p hl hM ha initial target (hsa.tail hm) hbt ht)

end Solution
end PushPuzzle.PushS.PortLayout

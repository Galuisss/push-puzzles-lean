/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortDeeperBudget
public import PushS.PortEndpointReaderFreeze
public import PushS.PortInstance
public import PushS.EndpointWalking
public import PushS.Radius
public import PushS.Blocked
import all PushS.PortDeeperBudget
import all PushS.EndpointWalking
import all PushS.PortEndpointLocality
import all PushS.PortEndpointCrossing
import all PushS.PortCentralStrip
import all PushS.PortStreetEnumeration
import all PushS.PortLayoutCoordinates
import all PushS.PortSegments
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! The actual ordinary f/r interlevel markers remain excluded after deeper public walks clear. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The two actual f/r column markers between each level-`j` endpoint and the next level. -/
@[expose] noncomputable def interlevelMarkers (l : PortLayout) (p : Scales.Parameters) (j : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => ∃ e ∈ l.endpoints, e.level = j ∧ e.level < p.levels ∧
    ∃ k : EndpointStreet, q.1.val = k.column p e ∧
      q.2.val = if e.side = .upper then (readDepth p e.level + readDepth p (e.level + 1)) / 2
        else p.H - (readDepth p e.level + readDepth p (e.level + 1)) / 2

private theorem marker_data (l : PortLayout) (p : Scales.Parameters) {j : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.interlevelMarkers p j) :
    ∃ e ∈ l.endpoints, e.level = j ∧ e.level < p.levels ∧
      ∃ k : EndpointStreet, q.1.val = k.column p e ∧
        q.2.val = if e.side = .upper then (readDepth p e.level + readDepth p (e.level + 1)) / 2
          else p.H - (readDepth p e.level + readDepth p (e.level + 1)) / 2 := by
  classical
  simpa only [interlevelMarkers, Finset.mem_filter, Finset.mem_univ, true_and] using hq

private theorem budget_outer (p : Scales.Parameters) {j : ℕ} (hj : j ≤ p.levels) :
    p.b j + 2 * columnRadius p + 2 * (p.Y p.levels + 2) + 8 < p.D := by
  have hy := Y_le p hj
  have hL := L_le p hj
  have hm := Nat.mul_le_mul_left (8 * (p.axes + 1))
    (show p.Y j + p.L j + 10 ≤ p.Y p.levels + p.L p.levels + 10 by omega)
  have hb : p.b j ≤ p.b p.levels := by unfold Scales.Parameters.b; omega
  have hmul := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
    (show 1 ≤ 8 * (p.axes + 1) by omega)
  simp only [Nat.one_mul] at hmul
  have hY : p.Y p.levels + 2 ≤ p.b p.levels := by unfold Scales.Parameters.b; omega
  have hd := p.outer_distance
  dsimp only [columnRadius]
  omega

private theorem middle_depth_bounds (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    p.b j < (readDepth p j + readDepth p (j + 1)) / 2 ∧
      (readDepth p j + readDepth p (j + 1)) / 2 + p.b j < p.H ∧
      (readDepth p j + readDepth p (j + 1)) / 2 ≤ p.Y p.levels := by
  have hg := readDepth_interlevel_margin p hj hjm
  have hy := readDepth_le_last p j
  have hn := readDepth_le_last p (j + 1)
  have ho := budget_outer p (le_of_lt hjm)
  have hH : p.H = 2 * p.D := rfl
  omega

private theorem marker_column_span (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet) :
    p.x e.port - columnRadius p ≤ k.column p e ∧ k.column p e ≤ p.x e.port + columnRadius p := by
  apply endpoint_columns_span p e
  cases k <;> simp [endpointColumns, EndpointStreet.column]

private theorem endpoint_page_band (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    if e.side = .upper then q.2 ≤ p.Y p.levels + 2 else p.H ≤ q.2 + p.Y p.levels + 2 := by
  have hs := fixed_endpoint_page l p e hq
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  have hb := endpointFixed_band l p e s hmem q hq
  dsimp only [LayerBand] at hb
  have hm := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  cases hside : e.side <;> simp only [hside, reduceCtorEq, ite_true, ite_false] at hs ⊢ <;> omega

/-- Every actual interlevel marker is a literal fixed hole in every emitted signal state. -/
theorem interlevelMarkers_subset_encoded (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState) (j : ℕ) :
    l.interlevelMarkers p j ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨e, he, _, hm, k, hx, hy⟩ := marker_data l p hq
  let c := coordinates p
  let s := point (k.column p e) (onSide c e.side ((c.depth e.level + c.depth (e.level + 1)) / 2))
  have hs : s ∈ endpointFixedSegments l c e := by
    simp only [endpointFixedSegments, List.mem_append]
    apply Or.inr
    rw [ite_eq_left (show e.level < c.levels from hm)]
    cases k <;> simp only [s, EndpointStreet.column, List.mem_cons, List.not_mem_nil, or_false]
    · exact Or.inl rfl
    · exact Or.inr rfl
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.endpointFixedSegments_mem_fixed p hl hM e he hs), ?_⟩
  have hy' : q.2.val = onSide c e.side ((c.depth e.level + c.depth (e.level + 1)) / 2) := hy
  simp only [s, point, segment, Segment.Contains, Nat.min_self, Nat.max_self]
  simp only [hx, hy', le_refl, and_self, true_or]

private theorem frame_marker_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {j : ℕ} (hj : 1 ≤ j) {e : Endpoint} (he : e ∈ l.endpoints)
    (hjm : j < p.levels) (k : EndpointStreet)
    {q a : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = k.column p e)
    (hy : q.2.val = if e.side = .upper then (readDepth p j + readDepth p (j + 1)) / 2
      else p.H - (readDepth p j + readDepth p (j + 1)) / 2)
    (hframe : a ∈ Boundary.frame) : p.b j < distance a q := by
  have hspan := marker_column_span p e k
  rw [← hx] at hspan
  have ho := budget_outer p (le_of_lt hjm)
  have hd := middle_depth_bounds p hj hjm
  have hleft : p.D ≤ p.x e.port := by
    have hm := Nat.mul_le_mul_right p.D (show 1 ≤ e.port + 1 by omega)
    simpa only [Nat.one_mul, Scales.Parameters.x] using hm
  have hright : p.x e.port + p.D ≤ p.W := by
    have hm := axis_spacing p (lt_of_lt_of_le (l.endpoints_port_lt hl he) ha)
    simpa only [Scales.Parameters.x, Scales.Parameters.W] using hm
  obtain ⟨d, hboundary⟩ := (Boundary.mem_frame a).mp hframe
  cases d <;>
    simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hboundary <;>
    simp only [distance, Nat.dist_eq_max_sub_min] <;>
    cases hside : e.side <;> simp only [hside, reduceCtorEq, ite_true, ite_false] at hy <;> omega

private theorem distinct_axis_far (p : Scales.Parameters) {j i k : ℕ} (hne : k ≠ i)
    (hD : p.b j + 2 * columnRadius p < p.D)
    {a q : Cell (p.W + 1) (p.H + 1)}
    (ha : p.x k - columnRadius p ≤ a.1.val ∧ a.1.val ≤ p.x k + columnRadius p)
    (hq : p.x i - columnRadius p ≤ q.1.val ∧ q.1.val ≤ p.x i + columnRadius p) :
    p.b j < distance a q := by
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hgap := axis_spacing p hlt
    simp only [distance, Nat.dist_eq_max_sub_min]
    omega
  · have hgap := axis_spacing p hgt
    simp only [distance, Nat.dist_eq_max_sub_min]
    omega

/-- Every cell of the actual deeper public walks is farther than `b j` from an interlevel marker. -/
theorem interlevelMarkers_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {j : ℕ} (hj : 1 ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.interlevelMarkers p j) :
    ∀ a ∈ l.deeperWalkHoles p j, p.b j < distance a q := by
  obtain ⟨e, he, hej, hem, k, hx, hy⟩ := marker_data l p hq
  have hjm : j < p.levels := by omega
  simp only [hej] at hy
  intro a haP
  rcases Finset.mem_union.mp haP with hframe | hwalk
  · exact frame_marker_far l p hl ha hj he hjm k hx hy hframe
  obtain ⟨s, hs, hac⟩ := (SegmentRecipe.mem_holes _ a).mp hwalk
  obtain ⟨f, hf, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨hf, hflevel⟩ := List.mem_filter.mp hf
  have hlevel : j < f.level := of_decide_eq_true hflevel
  have haf : (a.1.val, a.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) f) :=
    (mem_pointHoles _ _).mpr ⟨s, List.mem_of_mem_take hs, hac⟩
  have hqspan := marker_column_span p e k
  rw [← hx] at hqspan
  have haspan := fixed_endpoint_span l p f haf
  have hL := readLength_le_last p f.level
  have ho := budget_outer p (le_of_lt hjm)
  by_cases hport : f.port = e.port
  · have hside : f.side ≠ e.side := by
      intro hs
      have heq := l.endpoints_key_injective hl hf he hs hport
      subst f
      omega
    have hband := endpoint_page_band l p f haf
    have hdepth := (middle_depth_bounds p hj hjm).2.2
    have hH : p.H = 2 * p.D := rfl
    cases hes : e.side <;> cases hfs : f.side <;>
      simp only [hes, hfs, ne_eq, reduceCtorEq, not_true_eq_false, ite_true, ite_false] at hside hband hy <;>
      simp only [distance, Nat.dist_eq_max_sub_min] <;> omega
  · apply distinct_axis_far p hport (by omega) ?_ hqspan
    dsimp only [columnRadius]
    omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

private theorem deeper_preserving_between {u v t : State (p.W + 1) (p.H + 1)} (j : ℕ)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (huv : Reachable (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) :
    Relation.ReflTransGen (Radius.PreservingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.deeperWalkHoles p j)) u v := by
  revert hvt
  induction huv with
  | refl => exact fun _ => .refl
  | @tail v w huv hm ih =>
    intro hwt
    exact (ih ((Relation.ReflTransGen.single hm).trans hwt)).tail
      ⟨hm, hP w ((hsu.trans huv).tail hm) hwt⟩

private theorem interlevel_actual_far {j : ℕ} (hj : 1 ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.interlevelMarkers p j) :
    ∀ a ∈ l.deeperWalkHoles p j,
      (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p j).card <
        distance a q := by
  have hbudget : (holes (l.physicalInstance p hl hM ha initial target).initial \ l.deeperWalkHoles p j).card ≤ p.b j := by
    rw [l.physicalInstance_initial_holes p hl hM ha initial target]
    exact l.encodedSegments_outside_deeperWalk_card_le p hl hM ha initial hj
  exact fun a hap => hbudget.trans_lt (l.interlevelMarkers_far p hl ha hj hq a hap)

/-- Actual ordinary interlevel markers stay empty and unvisited once deeper public walks stay empty. -/
theorem physicalInstance_interlevel_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) :
    Blocked.Excluded (l.interlevelMarkers p j) u := by
  have hsu' := deeper_preserving_between l p hl hM ha initial target j .refl hsu hut hP
  have hut' := deeper_preserving_between l p hl hM ha initial target j hsu hut .refl hP
  have hPi := hP _ .refl (hsu.trans hut)
  have hp : (l.physicalInstance p hl hM ha initial target).initial.player ∈ l.deeperWalkHoles p j :=
    Finset.mem_union_left _ (l.physicalInstance_initial_frame p hl hM ha initial target)
  constructor
  · intro q hq
    have hfinal : q ∈ holes t := by
      change q ∈ t.boxesᶜ
      rw [ht]
      change q ∈ (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ
      rw [compl_compl]
      exact l.interlevelMarkers_subset_encoded p hl hM target j hq
    exact Radius.distant_hole_at hsu' hut' hPi hp (interlevel_actual_far l p hl hM ha initial target hj hq) hfinal
  · intro hq
    exact Radius.player_ne_distant hsu' hPi hp (interlevel_actual_far l p hl hM ha initial target hj hq) rfl

/-- Each actual successful step also avoids the protected interlevel holes. -/
theorem physicalInstance_interlevel_step_avoiding {u v t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hm : Step (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) :
    Freeze.AvoidingStep (l.physicalInstance p hl hM ha initial target).board none
      (l.pageBlockers p hl ∪ l.interlevelMarkers p j) u v :=
  (step_page_avoiding l p hl hM ha initial target hsu hm hvt ht).union_excluded
    (l.physicalInstance_interlevel_excluded_at p hl hM ha initial target j hj
      hsu ((Relation.ReflTransGen.single hm).trans hvt) ht hP)
    (l.physicalInstance_interlevel_excluded_at p hl hM ha initial target j hj (hsu.tail hm) hvt ht hP)

/-- Every actual prefix avoids the page blockers together with the protected interlevel holes. -/
theorem physicalInstance_interlevel_avoiding_prefix {u t : State (p.W + 1) (p.H + 1)}
    (j : ℕ) (hj : 1 ≤ j)
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none
      (l.pageBlockers p hl ∪ l.interlevelMarkers p j))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply enrich_path hsu
  intro a b hsa hm hbu
  exact l.physicalInstance_interlevel_step_avoiding p hl hM ha initial target j hj hsa hm
    (hbu.trans hut) ht hP

/-- Filling the actual interlevel markers preserves the complete successful trajectory. -/
theorem physicalInstance_interlevel_fill {t : State (p.W + 1) (p.H + 1)} (j : ℕ) (hj : 1 ≤ j)
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p j ⊆ holes s) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill (l.physicalInstance p hl hM ha initial target).initial (l.interlevelMarkers p j))
      (Blocked.fill t (l.interlevelMarkers p j)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) hr
    (fun _ hsu hut => l.physicalInstance_interlevel_excluded_at p hl hM ha initial target j hj hsu hut ht hP)
  rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
  exact Finset.disjoint_empty_right _

/-- The first descending layer of actual interlevel markers is certified by the completed
last-level public-walk theorem. -/
theorem physicalInstance_interlevel_last_excluded (hlevels : 2 ≤ p.levels)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Blocked.Excluded (l.interlevelMarkers p (p.levels - 1)) u :=
  l.physicalInstance_interlevel_excluded_at p hl hM ha initial target (p.levels - 1) (by omega)
    hsu hut ht (fun _ hs ht' => l.physicalInstance_deeperWalk_last_empty p hl hM ha initial target hs ht' ht)

end Solution

end PushPuzzle.PushS.PortLayout

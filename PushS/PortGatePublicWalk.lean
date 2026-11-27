/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateBottomWall
public import PushS.PortPublicWalkBudget
import all PushS.PortDeeperBudget
import all PushS.PortGatePageWindow
import all PushS.PortGateBottomWall
import all PushS.PortPageBackground
import all PushS.PortStreetSupport
import all PushS.PortStreetSeparation
import all PushS.PortBackground
import all PushS.PortSegments

/-! Permanent emptiness of the four actual public long columns of every three-port gate. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The frame and the four actual public gate columns, stopping just before the work row. -/
noncomputable def gatePublicWalk (p : Scales.Parameters) (middle : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Boundary.frame ∪ Finset.univ.filter fun q =>
    q.1.val ∈ gatePublicColumns p middle ∧ p.H - readDepth p 1 < q.2.val

private theorem mem_gatePublicWalk (p : Scales.Parameters) (middle : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)} : q ∈ gatePublicWalk p middle ↔
    q ∈ Boundary.frame ∨ (q.1.val ∈ gatePublicColumns p middle ∧ p.H - readDepth p 1 < q.2.val) := by
  classical
  simp only [gatePublicWalk, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The emitted four public fixed segments belong to this exact finite walk. -/
theorem gatePublicSegments_subset_walk (p : Scales.Parameters) (middle : ℕ) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) ((gateFixedSegments (coordinates p) middle).take 4) ⊆
      gatePublicWalk p middle := by
  intro q hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hd : (coordinates p).depth 1 = readDepth p 1 := rfl
  have hc : (coordinates p).x = p.x := rfl
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hm := readDepth_add_lt_H p 1
  simp only [gateFixedSegments, List.map_cons, List.map_nil, List.cons_append,
    List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hs
  apply (mem_gatePublicWalk p middle).mpr
  right
  rcases hs with rfl | rfl | rfl | rfl
  all_goals
    have hp := vertical_coordinates hq
    simp only [gate_lower_coordinate, hd, hc] at hp
    refine ⟨?_, by omega⟩
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false, hp.1]
    tauto

/-- The complete physical emitter starts every actual public gate walk empty. -/
theorem gatePublicWalk_subset_encoded (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    gatePublicWalk p middle ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  rcases (mem_gatePublicWalk p middle).mp hq with hf | ⟨hx, hy⟩
  · exact l.encodedSegments_frame_subset p state hf
  by_cases hframe : q ∈ Boundary.frame
  · exact l.encodedSegments_frame_subset p state hframe
  have hqH : q.2.val < p.H := by
    have hb := q.2.isLt
    have hne : q.2.val ≠ p.H := fun h => hframe ((Boundary.mem_frame q).mpr
      ⟨.south, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩)
    omega
  let s := segment q.1.val (p.H - 1) q.1.val (p.H - (readDepth p 1 - 1))
  have hs : s ∈ gateFixedSegments (coordinates p) middle := by
    have hc : (coordinates p).x = p.x := rfl
    simp only [gateFixedSegments, List.mem_append]
    left
    left
    apply List.mem_map.mpr
    exact ⟨q.1.val, by simpa only [gatePublicColumns, hc] using hx, rfl⟩
  apply (SegmentRecipe.mem_holes _ q).mpr
  refine ⟨s, List.mem_append_left _ (l.gateFixedSegments_mem_fixed p hi hs), ?_⟩
  have hY := readDepth_ge p (show 1 ≤ 1 by omega) p.levels_pos
  have hm := readDepth_add_lt_H p 1
  apply Or.inl
  simp only [s, segment, Nat.min_self, Nat.max_self]
  simp only [true_and]
  constructor <;> omega

private theorem gate_walk_not_row (l : PortLayout) (p : Scales.Parameters) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : p.H - readDepth p 1 < q.2.val) (hyH : q.2.val < p.H) : q.2 ∉ l.workingRowSet p := by
  have hD := readDepth_add_lt_D p 1
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  intro hr
  rcases (l.workingRowSet_iff p q.2).mp hr with h0 | hH' | ⟨v, hv, hrow⟩
  · omega
  · omega
  · have hvmax := workingRows_le_last l p hv
    have hvmin := l.workingDepthCoordinates_gate_min p hi hv
    rcases hrow with hrow | hrow <;> omega

private noncomputable def gateLeftSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) : GateWideSeparator l p middle false :=
  Classical.choice (l.gateWideSeparator_nonempty p hl hM ha hi false)

private noncomputable def gateRightSeparator (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) : GateWideSeparator l p middle true :=
  Classical.choice (l.gateWideSeparator_nonempty p hl hM ha hi true)

/-- The actual page, special-column tails and two bottom bars protecting one gate's public walks. -/
noncomputable def gatePublicBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  ((l.pageFrozenBlockers p hl ∪ l.gateInterlevelMarkers p) ∪ l.gateTails p) ∪
    l.gateBottomWall p middle (gateLeftSeparator l p hl hM ha hi) (gateRightSeparator l p hl hM ha hi)

private theorem gate_public_page (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) : l.pageFrozenBlockers p hl ⊆ l.gatePublicBlockers p hl hM ha hi :=
  fun _ h => Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ h))

private theorem gate_public_cap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ gatePublicColumns p middle) (hy : q.2.val = p.H - (readDepth p 1 + 1)) :
    q ∈ l.gatePublicBlockers p hl hM ha hi := by
  rcases Finset.mem_union.mp (l.gateBottomWall_cap_mem p hl middle
    (gateLeftSeparator l p hl hM ha hi) (gateRightSeparator l p hl hM ha hi) hx hy) with hp | hw
  · exact gate_public_page l p hl hM ha hi hp
  · exact Finset.mem_union_right _ hw

/-- The actual four public columns have the computed frozen boundary on every possible incoming ray. -/
theorem gatePublicWalk_emptyBoundary (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) :
    Freeze.EmptyBoundary (gatePublicWalk p middle) Boundary.frame (l.gatePublicBlockers p hl hM ha hi) := by
  constructor
  intro d q a b hq hf hadj han hab
  have hq := ((mem_gatePublicWalk p middle).mp hq).resolve_left hf
  have hqH : q.2.val < p.H := by
    have hbound := q.2.isLt
    have hne : q.2.val ≠ p.H := fun h => hf ((Boundary.mem_frame q).mpr
      ⟨.south, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; omega⟩)
    omega
  have hrow := gate_walk_not_row l p hi hq.2 hqH
  have hcol : q.1 ∈ l.streetColumnSet p := by
    change q.1.val ∈ streetColumns l (coordinates p)
    exact pageColumn_mem_street l p hl .lower
      (l.gateSpecialColumn_mem_page p hi (gatePublicColumn_mem_special p hq.1))
  have heven := l.streetColumnSet_even p hcol
  have ha_out : ¬(a.1.val ∈ gatePublicColumns p middle ∧ p.H - readDepth p 1 < a.2.val) :=
    fun ha => han ((mem_gatePublicWalk p middle).mpr (Or.inr ha))
  cases d with
  | north =>
    have hb := a.2.isLt
    simp only [Adjacent] at hadj hab
    exact False.elim (ha_out ⟨hadj.1 ▸ hq.1, by omega⟩)
  | south =>
    simp only [Adjacent] at hadj hab
    right
    have hb : b.2.val = p.H - (readDepth p 1 + 1) := by
      have hY := readDepth_add_lt_H p 1
      have hqcol : a.1.val ∈ gatePublicColumns p middle := hadj.1 ▸ hq.1
      have hout : a.2.val ≤ p.H - readDepth p 1 := by by_contra! h; exact ha_out ⟨hqcol, h⟩
      omega
    exact gate_public_cap l p hl hM ha hi ((hadj.1.trans hab.1) ▸ hq.1) hb
  | east | west =>
    left
    apply gate_public_page l p hl hM ha hi
    apply off_page_blocker l p hl
    intro hp
    rcases pages_subset_streets l p hl hp with hc | hr
    · have hax := l.streetColumnSet_even p hc
      simp only [Adjacent] at hadj
      omega
    · exact hrow (hadj.2 ▸ hr)

/-- The actual finite gate bottom-wall closure starts from only page and special-marker blockers. -/
theorem gatePublicBlockers_closure (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.gateInterlevelMarkers p) (l.gatePublicBlockers p hl hM ha hi) :=
  l.gateBottomWall_closure p hl hM ha initial target hi
    (gateLeftSeparator l p hl hM ha hi) (gateRightSeparator l p hl hM ha hi)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

local notation "I" => l.physicalInstance p hl hM ha initial target

private theorem gate_frame_preserving {G : Finset (Cell (p.W + 1) (p.H + 1))}
    {u t : State (p.W + 1) (p.H + 1)}
    (hr : Relation.ReflTransGen (Freeze.AvoidingStep (I).board none G) (I).initial u)
    (hut : Reachable (I).board none u t) (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (fun a b => Freeze.AvoidingStep (I).board none G a b ∧
      Boundary.frame ⊆ holes b) (I).initial u := by
  apply enrich_path hr
  intro a b _ hm hbu
  refine ⟨hm, ?_⟩
  have hbt : Reachable (I).board none b t :=
    (Relation.ReflTransGen.mono (fun _ _ h => h.1) _ _ hbu).trans hut
  have htf : Disjoint t.boxes Boundary.frame := by
    apply Finset.disjoint_left.mpr
    intro q hbox hf
    have hh := l.encodedSegments_frame_subset p target hf
    rw [← l.physicalInstance_goal_holes p hl hM ha initial target, ← ht] at hh
    exact (Finset.mem_compl.mp hh) hbox
  intro q hq
  exact (mem_holes _).mpr (fun hb => Finset.disjoint_left.mp (Boundary.reachable_frame_empty hbt htf) hb hq)

/-- Every successful actual physical trajectory keeps all four public long gate columns empty. -/
theorem physicalInstance_gate_publicWalk_empty {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u)
    (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    gatePublicWalk p middle ⊆ holes u := by
  have hr := (l.gatePublicBlockers_closure p hl hM ha initial target hi).reachable
    (l.physicalInstance_gate_marker_avoiding_prefix p hl hM ha initial target hsu hut ht)
  apply (l.gatePublicWalk_emptyBoundary p hl hM ha hi).reachable_holes
    (gate_frame_preserving l p hl hM ha initial target hr hut ht)
  change gatePublicWalk p middle ⊆
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ
  rw [compl_compl]
  exact l.gatePublicWalk_subset_encoded p initial hi

/-- All actual ordinary and three-port public long segments stay empty on every successful play. -/
theorem physicalInstance_allPublicWalk_empty {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u)
    (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    l.allPublicWalkHoles p ⊆ holes u := by
  intro q hq
  have hord := l.physicalInstance_ordinaryWalks_empty p hl hM ha initial target hsu hut ht
  rcases Finset.mem_union.mp hq with hf | hw
  · exact hord (Finset.mem_union_left _ hf)
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hw
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    apply hord
    apply Finset.mem_union_right
    apply (SegmentRecipe.mem_holes _ q).mpr
    refine ⟨s, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, ?_⟩, hs⟩, hq⟩
    have hj := (l.endpoints_level_bounds p hl hM he).1
    exact decide_eq_true (by omega)
  · obtain ⟨middle, hi, hs⟩ := List.mem_flatMap.mp hs
    exact l.physicalInstance_gate_publicWalk_empty p hl hM ha initial target hi hsu hut ht
      (gatePublicSegments_subset_walk p middle ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hq⟩))

end Solution
end PushPuzzle.PushS.PortLayout

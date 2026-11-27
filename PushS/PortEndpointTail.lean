/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortInterlevelFreeze
public import PushS.PortEndpointPageWindow
import all PushS.PortSegments
import all PushS.PortLayoutCoordinates
import all PushS.PortWalkBudget
import all PushS.PortStreetSeparation
import all PushS.PortCentralStrip
import all PushS.PortEndpointRWall
import all PushS.PortStreetSupport
import all PushS.EndpointWalking
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! Actual full column tails between an endpoint's work band and its interlevel marker. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Depth of an ordinary endpoint's two emitted interlevel markers. -/
@[expose] def endpointMarkerDepth (p : Scales.Parameters) (e : Endpoint) : ℕ :=
  (readDepth p e.level + readDepth p (e.level + 1)) / 2

/-- The f or r column after its work band, stopping just before the actual interlevel hole. -/
@[expose] noncomputable def endpointTail (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q => q.1.val = k.column p e ∧
    ∃ v, readDepth p e.level + 3 ≤ v ∧ v < endpointMarkerDepth p e ∧
      q.2.val = if e.side = .upper then v else p.H - v

private theorem mem_endpointTail (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointTail p e k ↔ q.1.val = k.column p e ∧
      ∃ v, readDepth p e.level + 3 ≤ v ∧ v < endpointMarkerDepth p e ∧
        q.2.val = if e.side = .upper then v else p.H - v := by
  classical
  simp only [endpointTail, Finset.mem_filter, Finset.mem_univ, true_and]

/-- Every selected depth is at most the current work band or at least the next work band. -/
theorem workingDepthCoordinates_interlevel_gap (l : PortLayout) (p : Scales.Parameters)
    {j v : ℕ} (hj : 1 ≤ j) (hjM : j < p.levels) (hv : v ∈ l.workingDepthCoordinates p) :
    v ≤ readDepth p j + 2 ∨ readDepth p (j + 1) - 2 ≤ v := by
  change v ∈ workingRows l (coordinates p) at hv
  obtain ⟨i, hi, hv⟩ := List.mem_flatMap.mp hv
  have hiM : i + 1 ≤ p.levels := by
    have hi := List.mem_range.mp hi
    change i < p.levels at hi
    omega
  have hc : (coordinates p).depth (i + 1) = readDepth p (i + 1) := rfl
  by_cases hij : i + 1 ≤ j
  · left
    have hle := readDepth_le_level p hij
    rw [← readDepth_eq p hj (by omega)] at hle
    dsimp only at hv
    split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      simp only [hc] at hv <;> omega
  · right
    have hle := readDepth_le_level p (show j + 1 ≤ i + 1 by omega)
    rw [← readDepth_eq p (by omega) hiM] at hle
    dsimp only at hv
    split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;>
      simp only [hc] at hv <;> omega

private theorem tail_not_working_row (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) : q.2 ∉ l.workingRowSet p := by
  obtain ⟨_, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hq
  obtain ⟨hj, _⟩ := l.endpoints_level_bounds p hl hM he
  have hgap := readDepth_interlevel_margin p hj heM
  have hmax := readDepth_le_last p e.level
  have hnext := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  intro hr
  rcases (l.workingRowSet_iff p q.2).mp hr with hn | hs | ⟨w, hw, hrow⟩
  · dsimp only [endpointMarkerDepth] at hvm
    cases hside : e.side <;> simp only [hside, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  · dsimp only [endpointMarkerDepth] at hvm
    cases hside : e.side <;> simp only [hside, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  · have hwmax := workingRows_le_last l p hw
    have hwgap := l.workingDepthCoordinates_interlevel_gap p hj heM hw
    dsimp only [endpointMarkerDepth] at hvm
    rcases hrow with hrow | hrow <;> cases hside : e.side <;>
      simp only [hside, reduceCtorEq, ite_true, ite_false] at hy <;> omega

private theorem tail_west_blocker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) :
    ∃ r, Adjacent .west q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hx := ((mem_endpointTail p e k q).mp hq).1
  have hx0 := readLength_add_lt_x p e.port e.level
  have hpos : 0 < q.1.val := by
    rw [hx]
    cases k <;> cases hi : e.inward <;>
      simp only [EndpointStreet.column_f, EndpointStreet.column_r, hi, Bool.false_eq_true, ite_true, ite_false] <;> omega
  have hcol : q.1 ∈ l.streetColumnSet p := by
    rw [l.streetColumnSet_iff, hx]
    cases k
    · exact (auxiliary_columns l p he).1
    · exact (auxiliary_columns l p he).2
  have hrow := tail_not_working_row l p hl hM e he heM k hq
  have heven := l.streetColumnSet_even p hcol
  let r : Cell (p.W + 1) (p.H + 1) := (⟨q.1.val - 1, by have := q.1.isLt; omega⟩, q.2)
  refine ⟨r, ⟨by change q.1.val - 1 + 1 = q.1.val; omega, rfl⟩, ?_⟩
  apply off_page_blocker l p hl
  intro hp
  rcases pages_subset_streets l p hl hp with hc | hr
  · have he := l.streetColumnSet_even p hc
    dsimp only [r] at he
    omega
  · exact hrow hr

private theorem tail_marker_ray (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : e ∈ l.endpoints) (heM : e.level < p.levels) (k : EndpointStreet)
    {G : Finset (Cell (p.W + 1) (p.H + 1))} (hmarkers : l.interlevelMarkers p e.level ⊆ G)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) :
    Freeze.Ray (endpointTail p e k) G (if e.side = .upper then .south else .north) q := by
  obtain ⟨hx, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hq
  have hmax := readDepth_le_last p e.level
  have hnext := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hmid : endpointMarkerDepth p e < p.H := by dsimp only [endpointMarkerDepth]; omega
  let n := endpointMarkerDepth p e - v - 1
  let path : Fin (n + 2) → Cell (p.W + 1) (p.H + 1) := fun i =>
    (q.1, ⟨if e.side = .upper then v + i.val else p.H - (v + i.val), by
      have := i.isLt; dsimp only [n] at *; split <;> omega⟩)
  have hstart : path 0 = q := by
    apply Prod.ext
    · rfl
    apply Fin.ext
    change (if e.side = .upper then v + 0 else p.H - (v + 0)) = q.2.val
    simpa only [Nat.add_zero] using hy.symm
  rw [← hstart]
  apply Freeze.Ray.of_path path
  · intro i
    have hi := i.isLt
    cases hs : e.side <;>
      simp only [path, Adjacent, hs, reduceCtorEq, ite_true, ite_false, Fin.val_succ, Fin.val_castSucc] <;>
      constructor <;> first | trivial | (dsimp only [n] at hi; omega)
  · intro i
    left
    apply (mem_endpointTail p e k _).mpr
    refine ⟨hx, v + (i.val + 1), by omega, ?_, rfl⟩
    have := i.isLt
    dsimp only [n] at *
    omega
  · apply hmarkers
    classical
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, e, he, rfl, heM, k, hx, ?_⟩
    change (if e.side = .upper then v + (n + 1) else p.H - (v + (n + 1))) = _
    have hn : v + (n + 1) = endpointMarkerDepth p e := by dsimp only [n]; omega
    rw [hn]
    rfl

/-- Each actual column tail is horizontally anchored to the page background and vertically
to its own emitted interlevel marker. -/
theorem endpointTail_anchored (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hmarkers : l.interlevelMarkers p e.level ⊆ G) : Freeze.Anchored (endpointTail p e k) G := by
  intro d q hq
  obtain ⟨r, ha, hr⟩ := tail_west_blocker l p hl hM e he heM k hq
  have hh : Freeze.Ray (endpointTail p e k) G .west q := .hit ha (hpage hr)
  have hv : Freeze.Ray (endpointTail p e k) G .north q ∨ Freeze.Ray (endpointTail p e k) G .south q := by
    have hm := tail_marker_ray l p e he heM k hmarkers hq
    cases hs : e.side
    · exact Or.inr (by simpa only [hs, ite_true] using hm)
    · exact Or.inl (by simpa only [hs, reduceCtorEq, ite_false] using hm)
  cases d with
  | north => exact hv
  | south => exact hv.symm
  | east => exact Or.inr hh
  | west => exact Or.inl hh

private theorem tail_ne_work_row (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) {u : ℕ}
    (hu : u ≤ readDepth p e.level + 2) : q.2.val ≠ onSide (coordinates p) e.side u := by
  obtain ⟨_, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hq
  have hm := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hH' : (coordinates p).H = p.H := rfl
  dsimp only [endpointMarkerDepth] at hvm
  cases hs : e.side <;> simp only [onSide, hs, reduceCtorEq, ite_true, ite_false, hH'] at hy ⊢ <;> omega

private theorem tail_ne_marker_row (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) :
    q.2.val ≠ onSide (coordinates p) e.side (endpointMarkerDepth p e) := by
  obtain ⟨_, v, _, hvm, hy⟩ := (mem_endpointTail p e k q).mp hq
  have hm := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hH' : (coordinates p).H = p.H := rfl
  dsimp only [endpointMarkerDepth] at *
  cases hs : e.side <;> simp only [onSide, hs, reduceCtorEq, ite_true, ite_false, hH'] at hy ⊢ <;> omega

private theorem own_fixed_tail_clear (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (k : EndpointStreet) {q : Cell (p.W + 1) (p.H + 1)} (hrod : q ∈ endpointTail p e k)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : False := by
  obtain ⟨_, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hrod
  have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
  have hH : (coordinates p).H = p.H := rfl
  have hm := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH' : p.H = 2 * p.D := rfl
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hc := (vertical_coordinates hq).2
    dsimp only [endpointMarkerDepth] at hvm
    cases hside : e.side <;> simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hc hy <;> omega
  · have hc := (vertical_coordinates hq).2
    dsimp only [endpointMarkerDepth] at hvm
    cases hside : e.side <;> simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hc hy <;> omega
  · exact tail_ne_work_row p e k hrod le_rfl (horizontal_coordinates hq).1
  · obtain ⟨u, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · rename_i hle
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact tail_ne_work_row p e k hrod (by change u ≤ readDepth p e.level at hle; omega)
          (point_coordinates hq).2
      · cases hs
    · split at hs
      · rename_i hlt
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact tail_ne_work_row p e k hrod (by change u < readDepth p e.level at hlt; omega)
          (point_coordinates hq).2
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl <;> exact tail_ne_marker_row p e k hrod (point_coordinates hq).2
    · cases hs

private theorem own_signal_tail_clear (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    (k : EndpointStreet) {q : Cell (p.W + 1) (p.H + 1)} (hrod : q ∈ endpointTail p e k)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state e)) : False := by
  obtain ⟨_, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hrod
  have hd : (coordinates p).depth e.level = readDepth p e.level := rfl
  have hH : (coordinates p).H = p.H := rfl
  have hm := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hY := last_depth_margin p
  have hH' : p.H = 2 * p.D := rfl
  have hb := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hc := (vertical_coordinates hq).2
    dsimp only [endpointMarkerDepth] at hvm
    cases hside : e.side <;> simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, hd, hH] at hc hy hb <;> omega
  · exact tail_ne_work_row p e k hrod (by omega) (horizontal_coordinates hq).1

private theorem tail_page_window (p : Scales.Parameters) (e : Endpoint) (k : EndpointStreet)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointTail p e k) : q ∈ endpointPageWindow p e := by
  obtain ⟨hx, v, hv, hvm, hy⟩ := (mem_endpointTail p e k q).mp hq
  have hm := readDepth_le_last p e.level
  have hn := readDepth_le_last p (e.level + 1)
  have hlen := readLength_le_last p e.level
  have hx0 := readLength_add_lt_x p e.port e.level
  have hY := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  dsimp only [endpointMarkerDepth] at hvm
  constructor
  · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
  · rw [hx]
    cases k <;> cases hi : e.inward <;>
      simp only [EndpointStreet.column_f, EndpointStreet.column_r, hi, Bool.false_eq_true,
        ite_true, ite_false, Nat.dist] <;> omega

/-- Every actual f/r tail is initially full in every physical signal configuration. -/
theorem endpointTail_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints) (k : EndpointStreet) :
    endpointTail p e k ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hrod
  by_contra hbox
  have hh := (mem_holes _).mpr hbox
  rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
  change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) at hh
  rw [l.encodedSegments_endpointPageWindow p hl hM ha initial e he q (tail_page_window p e k hrod)] at hh
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hh
  rcases List.mem_append.mp hs with hs | hs
  · exact own_fixed_tail_clear l p e k hrod ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
  · exact own_signal_tail_clear p initial e k hrod ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)

/-- The actual interlevel holes and page closure freeze the complete f/r column tail. -/
theorem endpointTail_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.interlevelMarkers p e.level)
      ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e k) := by
  have hc : Freeze.Closure (w := p.W + 1) (h := p.H + 1)
      (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.interlevelMarkers p e.level)
      (l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) :=
    (l.pageBackground_closure p hl hM ha initial target).adjoin_blockers (l.interlevelMarkers p e.level)
  exact .add hc (l.endpointTail_initial_full p hl hM ha initial target e he k)
    (l.endpointTail_anchored p hl hM e he heM k _ Finset.subset_union_left Finset.subset_union_right)

/-- Once deeper public walks are empty, every actual successful push avoids the complete
column tail up to the protected interlevel marker. -/
theorem physicalInstance_endpoint_tail_avoiding (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals)
    (hP : ∀ s, Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial s →
      Reachable (l.physicalInstance p hl hM ha initial target).board none s t →
      l.deeperWalkHoles p e.level ⊆ holes s) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none
      ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e k))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply (l.endpointTail_closure p hl hM ha initial target e he heM k).reachable
  exact l.physicalInstance_interlevel_avoiding_prefix p hl hM ha initial target e.level
    (l.endpoints_level_bounds p hl hM he).1 hsu hut ht hP

/-- The first cell beyond an actual work band belongs to its computed full column tail. -/
theorem endpointTail_start_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    (heM : e.level < p.levels) (k : EndpointStreet) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = k.column p e)
    (hy : q.2.val = if e.side = .upper then readDepth p e.level + 3
      else p.H - (readDepth p e.level + 3)) : q ∈ endpointTail p e k := by
  have hj := (l.endpoints_level_bounds p hl hM he).1
  have hg := readDepth_interlevel_margin p hj heM
  apply (mem_endpointTail p e k q).mpr
  refine ⟨hx, readDepth p e.level + 3, le_rfl, ?_, hy⟩
  dsimp only [endpointMarkerDepth]
  omega

/-- The tails on the first descending level are frozen directly from the completed last-level
public-walk theorem. -/
theorem physicalInstance_penultimate_tail_avoiding (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    (heL : e.level + 1 = p.levels) (k : EndpointStreet) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none
      ((l.pageFrozenBlockers p hl ∪ l.interlevelMarkers p e.level) ∪ endpointTail p e k))
      (l.physicalInstance p hl hM ha initial target).initial u := by
  apply l.physicalInstance_endpoint_tail_avoiding p hl hM ha initial target e he (by omega) k hsu hut ht
  intro s hs ht'
  have hep : e.level = p.levels - 1 := by omega
  simpa only [hep] using l.physicalInstance_deeperWalk_last_empty p hl hM ha initial target hs ht' ht

end PushPuzzle.PushS.PortLayout

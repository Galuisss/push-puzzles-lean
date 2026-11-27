/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointFStock
public import PushS.PortReaderFreeze
public import PushS.PortEndpointBranch
import all PushS.PortEndpointCaps
import all PushS.PortEndpointWide
import all PushS.PortEndpointLocality
import all PushS.PortEndpointSeparation
import all PushS.PortSegments
import all PushS.PortStreetSupport
import all PushS.EndpointWalking
import all PushS.PortCentralStrip
import all PushS.PortPageBackground
import all PushS.PortBackground

/-! Actual f-side half rods between the reader midpoints and ordinary axes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- The solid part of a selected f-side row from its midpoint towards the ordinary axis. -/
@[expose] noncomputable def endpointFrontRod (p : Scales.Parameters) (e : Endpoint) (v : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) := by
  classical
  exact Finset.univ.filter fun q =>
    q.2.val = (if e.side = .upper then v else p.H - v) ∧
      (if e.inward then (EndpointStreet.f.column p e + p.x e.port) / 2 < q.1.val ∧ q.1.val < p.x e.port
        else p.x e.port < q.1.val ∧ q.1.val < (EndpointStreet.f.column p e + p.x e.port) / 2)

private theorem mem_endpointFrontRod (p : Scales.Parameters) (e : Endpoint) (v : ℕ)
    (q : Cell (p.W + 1) (p.H + 1)) :
    q ∈ endpointFrontRod p e v ↔
      q.2.val = (if e.side = .upper then v else p.H - v) ∧
      (if e.inward then (EndpointStreet.f.column p e + p.x e.port) / 2 < q.1.val ∧ q.1.val < p.x e.port
        else p.x e.port < q.1.val ∧ q.1.val < (EndpointStreet.f.column p e + p.x e.port) / 2) := by
  classical
  simp only [endpointFrontRod, Finset.mem_filter, Finset.mem_univ, true_and]

private theorem front_geometry (p : Scales.Parameters) (e : Endpoint) {v : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointFrontRod p e v) :
    (if e.inward then EndpointStreet.f.column p e < q.1.val ∧ q.1.val < p.x e.port
      else p.x e.port < q.1.val ∧ q.1.val < EndpointStreet.f.column p e) ∧
      Nat.dist q.1.val (p.x e.port) ≤ readLength p e.level ∧
      q.1.val ≠ (EndpointStreet.f.column p e + p.x e.port) / 2 := by
  have hq := ((mem_endpointFrontRod p e v q).mp hq).2
  have hx := readLength_add_lt_x p e.port e.level
  cases hi : e.inward <;>
    simp only [EndpointStreet.column_f, hi, Bool.false_eq_true, ite_true, ite_false, Nat.dist] at hq ⊢ <;> omega

private theorem front_window (p : Scales.Parameters) (e : Endpoint) {v : ℕ}
    (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointFrontRod p e v) : q ∈ endpointWindow p e := by
  have hgeom := front_geometry p e hq
  have hy := ((mem_endpointFrontRod p e v q).mp hq).1
  have hH := readDepth_add_lt_H p e.level
  constructor
  · cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
  · omega

private theorem own_fixed_front_clear (l : PortLayout) (p : Scales.Parameters)
    (e : Endpoint)
    {v : ℕ} (hvy : v ≤ readDepth p e.level) {q : Cell (p.W + 1) (p.H + 1)}
    (hrod : q ∈ endpointFrontRod p e v)
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : False := by
  let c := coordinates p
  obtain ⟨hbetween, _, hmid⟩ := front_geometry p e hrod
  have hrow := ((mem_endpointFrontRod p e v q).mp hrod).1
  have hY : c.depth e.level + 64 < c.H := readDepth_add_lt_H p e.level
  have hL : c.length e.level + 64 < c.x e.port := readLength_add_lt_x p e.port e.level
  change v ≤ c.depth e.level at hvy
  change q.2.val = onSide c e.side v at hrow
  change (q.1.val, q.2.val) ∈ pointHoles (endpointFixedSegments l c e) at hq
  change (if e.inward then (auxiliary c e).1 < q.1.val ∧ q.1.val < c.x e.port
    else c.x e.port < q.1.val ∧ q.1.val < (auxiliary c e).1) at hbetween
  change q.1.val ≠ ((auxiliary c e).1 + c.x e.port) / 2 at hmid
  have hinner (d : ℕ) : q.1.val ≠ inward (c.x e.port) e.inward d := by
    intro heq
    cases hi : e.inward <;>
      simp only [inward, hi, Bool.false_eq_true, ite_true, ite_false] at heq hbetween <;> omega
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ _).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hp := (vertical_coordinates hq).1
    cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hbetween <;> omega
  · have hp := (vertical_coordinates hq).1
    exact hinner 2 hp
  · have hp := (horizontal_coordinates hq).1
    cases hs : e.side <;> simp only [onSide, hs, reduceCtorEq, ite_true, ite_false] at hp hrow <;> omega
  · obtain ⟨y, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        exact hmid (point_coordinates hq).1
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hp := (point_coordinates hq).1
        exact hinner 1 hp
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · have hp := (point_coordinates hq).1
        cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hbetween <;> omega
      · exact hinner 2 (point_coordinates hq).1
    · cases hs

/-- The cell just outward of an ordinary axis belongs to its actual midpoint half rod. -/
theorem endpointFrontRod_back_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = if e.inward then p.x e.port - 1 else p.x e.port + 1)
    (hy : q.2.val = if e.side = .upper then v else p.H - v) : q ∈ endpointFrontRod p e v := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hlen := readLength_ge p hj hm
  have hx0 := readLength_add_lt_x p e.port e.level
  refine (mem_endpointFrontRod p e v q).mpr ⟨hy, ?_⟩
  cases hi : e.inward <;>
    simp only [EndpointStreet.column_f, hi, Bool.false_eq_true, ite_true, ite_false] at hx ⊢ <;> omega

/-- Every actual f-side half rod is initially full for every physical signal state. -/
theorem endpointFrontRod_initial_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) (e : Endpoint) (he : e ∈ l.endpoints)
    {v : ℕ} (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level) :
    endpointFrontRod p e v ⊆ (l.physicalInstance p hl hM ha initial target).initial.boxes := by
  intro q hrod
  by_contra hbox
  have hh := (mem_holes _).mpr hbox
  rw [l.physicalInstance_initial_holes p hl hM ha initial target] at hh
  change q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial) at hh
  rw [l.encodedSegments_endpointWindow p hl hM ha initial e he q (front_window p e hv hvy hrod)] at hh
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hh
  rcases List.mem_append.mp hs with hs | hs
  · exact own_fixed_front_clear l p e hvy hrod ((mem_pointHoles _ _).mpr ⟨s, hs, hq⟩)
  · have hbetween := (front_geometry p e hrod).1
    have hcoord : (coordinates p).x e.port = p.x e.port := rfl
    dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hp := (vertical_coordinates hq).1
      rw [hcoord] at hp
      cases hi : e.inward <;> simp only [hi, Bool.false_eq_true, ite_true, ite_false] at hbetween <;> omega
    · have hp := (horizontal_coordinates hq).2
      rw [hcoord] at hp
      have hx := readLength_add_lt_x p e.port e.level
      cases hi : e.inward <;> simp only [EndpointStreet.column_f, inward, hi, Bool.false_eq_true, ite_true, ite_false] at hp hbetween <;> omega

private theorem front_not_page_column (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointFrontRod p e v) :
    q.1 ∉ l.pageColumnSet p e.side := by
  intro hc
  have hgeom := front_geometry p e hq
  have hlen := readLength_le_last p e.level
  have hx := readLength_add_lt_x p e.port e.level
  have hfcol : (auxiliary (coordinates p) e).1 = EndpointStreet.f.column p e := rfl
  have hrcol : (auxiliary (coordinates p) e).2 = EndpointStreet.r.column p e := rfl
  rcases nearby_page_columns l p hl ha he hc (by omega) with hc | hc | hc <;>
    cases hi : e.inward <;>
    simp only [hfcol, hrcol, EndpointStreet.column_f, EndpointStreet.column_r, hi,
      Bool.false_eq_true, ite_true, ite_false] at hc hgeom <;> omega

private theorem front_north_blocker (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
    (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level) (hsel : v ∈ l.workingDepthCoordinates p)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ endpointFrontRod p e v) :
    ∃ r, Adjacent .north q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hy := ((mem_endpointFrontRod p e v q).mp hq).1
  have hY := last_depth_margin p
  have hmax := readDepth_le_last p e.level
  have hH : p.H = 2 * p.D := rfl
  have heven := l.workingRowSet_even p (l.mem_workingRowSet_of_onSide p hsel e.side q.2 hy)
  have hqpos : 0 < q.2.val := by
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy <;> omega
  let r : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨q.2.val - 1, by have := q.2.isLt; omega⟩)
  have hrow : r.2 ∉ l.workingRowSet p := by
    intro hr
    have he := l.workingRowSet_even p hr
    dsimp only [r] at he
    omega
  have hside : if e.side = .upper then r.2.val < p.D else p.D < r.2.val := by
    dsimp only [r]
    cases hs : e.side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hy ⊢ <;> omega
  have hoff : r ∉ (l.twoPageStreets p hl).support := by
    intro hp
    rcases (l.page_support_iff_side p hl e.side r hside).mp hp with hr | hc
    · exact hrow hr
    · exact front_not_page_column l p hl ha e he hq hc
  refine ⟨r, ⟨rfl, by change q.2.val - 1 + 1 = q.2.val; omega⟩, ?_⟩
  by_cases hc : r ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((l.mem_pageBackgroundBoxes p hl r).mpr ⟨hoff, hc⟩))

/-- The actual half rod is anchored once its emitted midpoint is an established blocker. -/
theorem endpointFrontRod_anchored (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
    (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level) (hsel : v ∈ l.workingDepthCoordinates p)
    (G : Finset (Cell (p.W + 1) (p.H + 1))) (hpage : l.pageFrozenBlockers p hl ⊆ G)
    (hmid : ∀ g : Cell (p.W + 1) (p.H + 1),
      g.1.val = (EndpointStreet.f.column p e + p.x e.port) / 2 →
      g.2.val = (if e.side = .upper then v else p.H - v) → g ∈ G) :
    Freeze.Anchored (endpointFrontRod p e v) G := by
  intro d q hq
  obtain ⟨r, ha', hr⟩ := front_north_blocker l p hl ha e he hv hvy hsel hq
  have hn : Freeze.Ray (endpointFrontRod p e v) G .north q := .hit ha' (hpage hr)
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le ha) e.level
  have hx0 := readLength_add_lt_x p e.port e.level
  have hq' := (mem_endpointFrontRod p e v q).mp hq
  let mid := (EndpointStreet.f.column p e + p.x e.port) / 2
  have hm : mid < p.W + 1 := by
    dsimp only [mid]
    cases hi : e.inward <;> simp only [EndpointStreet.column_f, hi, Bool.false_eq_true, ite_true, ite_false] <;> omega
  let g : Cell (p.W + 1) (p.H + 1) := (⟨mid, hm⟩, q.2)
  have hg : g ∈ G := hmid g rfl hq'.1
  have hh : Freeze.Ray (endpointFrontRod p e v) G .east q ∨
      Freeze.Ray (endpointFrontRod p e v) G .west q := by
    cases hi : e.inward
    · simp only [hi, Bool.false_eq_true, ite_false] at hq'
      left
      apply Freeze.Ray.east_of_interval (q := q) (g := g) rfl hq'.2.2 hg
      intro z hz hleft hright
      left
      apply (mem_endpointFrontRod p e v z).mpr
      exact ⟨(congrArg Fin.val hz).trans hq'.1, by simp only [hi, Bool.false_eq_true, ite_false]; dsimp only [g, mid] at hright; omega⟩
    · simp only [hi, ite_true] at hq'
      right
      apply Freeze.Ray.west_of_interval (q := q) (g := g) rfl hq'.2.1 hg
      intro z hz hleft hright
      left
      apply (mem_endpointFrontRod p e v z).mpr
      exact ⟨(congrArg Fin.val hz).trans hq'.1, by simp only [hi, ite_true]; dsimp only [g, mid] at hleft; omega⟩
  cases d with
  | north => exact Or.inl hn
  | south => exact Or.inr hn
  | east => exact hh
  | west => exact hh.symm

/-- The actual page closure and reader midpoint holes freeze a whole selected half rod. -/
theorem endpointFrontRod_closure (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
    (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level) (hsel : v ∈ l.workingDepthCoordinates p) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.readerMidpointRows p e.level)
      ((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p e.level) ∪ endpointFrontRod p e v) := by
  have hc : Freeze.Closure (w := p.W + 1) (h := p.H + 1)
      (l.physicalInstance p hl hM ha initial target).initial
      (l.pageBlockers p hl ∪ l.readerMidpointRows p e.level)
      (l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p e.level) :=
    (l.pageBackground_closure p hl hM ha initial target).adjoin_blockers (l.readerMidpointRows p e.level)
  apply Freeze.Closure.add hc (l.endpointFrontRod_initial_full p hl hM ha initial target e he hv hvy)
  apply l.endpointFrontRod_anchored p hl ha e he hv hvy hsel _ Finset.subset_union_left
  intro g hx hy
  apply Finset.mem_union_right
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, e, he, rfl, hx, v, hsel, hvy, hy⟩

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)
  (e : Endpoint) (he : e ∈ l.endpoints) {v : ℕ}
  (hv : 1 ≤ v) (hvy : v ≤ readDepth p e.level) (hsel : v ∈ l.workingDepthCoordinates p)

include he hv hvy hsel

local notation "I" => l.physicalInstance p hl hM ha initial target

/-- Once the actual reader walks are empty, every successful push avoids the f-side half rod. -/
theorem physicalInstance_endpoint_front_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals)
    (hP : ∀ s, Reachable (I).board none (I).initial s → Reachable (I).board none s t →
      l.readerWalkHoles p e.level ⊆ holes s) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      ((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p e.level) ∪ endpointFrontRod p e v))
      (I).initial u := by
  apply (l.endpointFrontRod_closure p hl hM ha initial target e he hv hvy hsel).reachable
  apply enrich_path hsu
  intro a b hsa hm hbu
  have hbt := hbu.trans hut
  have hAmid := l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target e.level
    hsa ((Relation.ReflTransGen.single hm).trans hbt) ht hP
  have hBmid := l.physicalInstance_reader_midpointRows_excluded_at p hl hM ha initial target e.level
    (hsa.tail hm) hbt ht hP
  have hp := step_page_avoiding l p hl hM ha initial target hsa hm hbt ht
  exact hp.union_excluded hAmid hBmid

/-- On the last level the complete actual half rod is frozen along every successful play. -/
theorem physicalInstance_last_front_avoiding (heM : e.level = p.levels)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (I).board none (I).initial u) (hut : Reachable (I).board none u t)
    (ht : t.boxes = (I).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep (I).board none
      ((l.pageFrozenBlockers p hl ∪ l.readerMidpointRows p e.level) ∪ endpointFrontRod p e v))
      (I).initial u := by
  apply l.physicalInstance_endpoint_front_avoiding p hl hM ha initial target e he hv hvy hsel hsu hut ht
  intro s hs ht'
  simpa only [heM] using l.physicalInstance_readerWalk_last_empty p hl hM ha initial target hs ht' ht

end Solution
end PushPuzzle.PushS.PortLayout

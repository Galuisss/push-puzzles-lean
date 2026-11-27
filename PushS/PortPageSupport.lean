/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.PortTwoPageStreets
public import PushS.PortStreetSupport
import all PushS.PortTwoPageStreets
import all PushS.PortStreetSupport
import all PushS.PortStreetSeparation
import all PushS.PortSegments
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.Blocked

/-!
# Actual two-page support of every successful prefix

The actual emitted target fits the specified page of each original auxiliary column. Filling
its permanent central markers leaves exactly the cut street support. Relative reverse support
then gives the same support at every filled prefix of an actual solution.
-/

public section
namespace PushPuzzle.PushS


open PushFS

namespace Support

/-- Enlarge the blocker set and temporarily include those blockers in the support. -/
theorem RelativeClosed.union_blockers {w h : ℕ} {C : Set (Cell w h)}
    {G K : Finset (Cell w h)} (hC : RelativeClosed C G) (hGK : G ⊆ K) :
    RelativeClosed (C ∪ (K : Set (Cell w h))) K := by
  intro d p q ha hp hq hpK hqK r hr
  have hs : StraightReach G d p r := Relation.ReflTransGen.mono
    (fun _ _ h => ⟨h.1, fun hg => h.2.1 (hGK hg), fun hg => h.2.2 (hGK hg)⟩) _ _ hr
  exact Or.inl (hC ha (hp.resolve_right hpK) (hq.resolve_right hqK)
    (fun hg => hpK (hGK hg)) (fun hg => hqK (hGK hg)) r hs)

private theorem supported_fill_iff {w h : ℕ} (C : Set (Cell w h))
    (K : Finset (Cell w h)) (s : State w h) :
    Supported C (Blocked.fill s K) ↔ Supported (C ∪ (K : Set (Cell w h))) s := by
  constructor
  · intro hs q hq
    by_cases hk : q ∈ K
    · exact Or.inr hk
    · exact Or.inl (hs q (by simpa [Blocked.fill] using And.intro hq hk))
  · intro hs q hq
    have hh : q ∉ s.boxes ∧ q ∉ K := by simpa [Blocked.fill] using hq
    exact (hs q hh.1).resolve_right hh.2

end Support

namespace PortLayout

open PushFS.Reduction SegmentRecipe

private def OnPages (l : PortLayout) (p : Scales.Parameters) (q : ℕ × ℕ) : Prop :=
  q.2 ∈ selectedRows l p ∨ q.1 ∈ mainColumnCoordinates l p ∨
    (q.1 ∈ pageColumnCoordinates l p .upper ∧ q.2 ≤ p.D) ∨
    (q.1 ∈ pageColumnCoordinates l p .lower ∧ p.D ≤ q.2)

private def PageSegment (l : PortLayout) (p : Scales.Parameters) (s : Segment) : Prop :=
  ∀ q, s.Contains q → OnPages l p q ∨ CentralBand p q

private def PageSegments (l : PortLayout) (p : Scales.Parameters) (ss : List Segment) : Prop :=
  ∀ s ∈ ss, PageSegment l p s

private theorem horizontal_page (l : PortLayout) (p : Scales.Parameters) {x u y : ℕ}
    (hy : y ∈ selectedRows l p) : PageSegment l p (segment x y u y) := by
  intro q hq
  exact Or.inl (Or.inl ((horizontal_coordinates hq).1 ▸ hy))

private theorem vertical_main (l : PortLayout) (p : Scales.Parameters) {x y v : ℕ}
    (hx : x ∈ mainColumnCoordinates l p) : PageSegment l p (segment x y x v) := by
  intro q hq
  exact Or.inl (Or.inr (Or.inl ((vertical_coordinates hq).1 ▸ hx)))

private theorem main_axis (l : PortLayout) (p : Scales.Parameters) {i : ℕ}
    (hi : i < l.portCount) : (coordinates p).x i ∈ mainColumnCoordinates l p :=
  List.mem_append_right _ (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)

private theorem endpoint_page_columns (l : PortLayout) (p : Scales.Parameters) {e : Endpoint}
    (he : e ∈ endpoints l) :
    (auxiliary (coordinates p) e).1 ∈ pageColumns l (coordinates p) e.side ∧
      (auxiliary (coordinates p) e).2 ∈ pageColumns l (coordinates p) e.side := by
  constructor
  all_goals apply endpoint_columns_mem l p e he; simp

private theorem special_page_column (l : PortLayout) (p : Scales.Parameters) {i x : ℕ}
    (hi : i ∈ centers l) (hx : x ∈ specialColumns (coordinates p) i) :
    x ∈ pageColumns l (coordinates p) .lower := by
  simp only [pageColumns, List.mem_append, or_assoc, ite_true]
  exact Or.inr (Or.inr (List.mem_flatMap.mpr ⟨i, hi, List.mem_cons_of_mem _ hx⟩))

private theorem vertical_page (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {x y v : ℕ} (hx : x ∈ pageColumns l (coordinates p) side)
    (hy : y ≤ p.D) (hv : v ≤ p.D) :
    PageSegment l p (segment x (onSide (coordinates p) side y) x (onSide (coordinates p) side v)) := by
  intro q hq
  have hcoords := (vertical_mem _ _ _ q).mp ((mem_pointHoles [_] q).mpr
    ⟨_, List.mem_singleton_self _, hq⟩)
  have hH : p.H = 2 * p.D := rfl
  apply Or.inl
  cases side with
  | upper =>
    apply Or.inr ∘ Or.inr ∘ Or.inl
    exact ⟨hcoords.1 ▸ hx, by simp only [onSide, ite_true] at hcoords; omega⟩
  | lower =>
    apply Or.inr ∘ Or.inr ∘ Or.inr
    refine ⟨hcoords.1 ▸ hx, ?_⟩
    simp only [onSide, reduceCtorEq, ite_false] at hcoords
    change _ ∧ min (p.H - y) (p.H - v) ≤ q.2 ∧ q.2 ≤ max (p.H - y) (p.H - v) at hcoords
    omega

private theorem central_page (l : PortLayout) (p : Scales.Parameters) {x y : ℕ}
    (hy : p.D ≤ y + 4 ∧ y ≤ p.D + 4) : PageSegment l p (point x y) := by
  intro q hq
  right
  change p.D ≤ q.2 + 4 ∧ q.2 ≤ p.D + 4
  rw [(point_coordinates hq).2]
  exact hy

private theorem endpointFixed_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ endpoints l) : PageSegments l p (endpointFixedSegments l (coordinates p) e) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hrows := workingRows_level l p hj hm
  obtain ⟨hf, hr⟩ := endpoint_page_columns l p he
  have hdepth := readDepth_add_lt_D p e.level
  have hnext := readDepth_add_lt_D p (e.level + 1)
  change (coordinates p).depth e.level + 64 < p.D at hdepth
  change (coordinates p).depth (e.level + 1) + 64 < p.D at hnext
  unfold PageSegments
  dsimp only [endpointFixedSegments]
  simp only [List.append_assoc]
  apply (List.forall_mem_append (p := PageSegment l p)).mpr
  constructor
  · intro s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · apply vertical_page l p e.side hf <;> omega
    · apply vertical_page l p e.side hr <;> omega
    · exact horizontal_page l p (row_onSide l p e.side hrows.2)
  · apply (List.forall_mem_append (p := PageSegment l p)).mpr
    constructor
    · apply (List.forall_mem_flatMap (p := PageSegment l p)).mpr
      intro y hy
      apply (List.forall_mem_append (p := PageSegment l p)).mpr
      constructor
      all_goals
        split
        · intro s hs
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          subst s
          exact horizontal_page l p (row_onSide l p e.side hy)
        · exact fun _ h => False.elim (List.not_mem_nil h)
    · split
      · intro s hs
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        rcases hs with rfl | rfl
        · apply vertical_page l p e.side hf <;> omega
        · apply vertical_page l p e.side hr <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem gateFixed_pages (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {i : ℕ} (hi : i ∈ centers l) : PageSegments l p (gateFixedSegments (coordinates p) i) := by
  have hcol : ∀ x ∈ specialColumns (coordinates p) i,
      x ∈ pageColumns l (coordinates p) .lower := fun _ hx => special_page_column l p hi hx
  obtain ⟨kind, first, hg, he⟩ := center_gate_mem l hi
  have hi' : i < l.portCount := by rw [he]; exact gate_middle_lt l hl hg
  have haxis := main_axis l p hi'
  have hrows := workingRows_level l p (j := 1) le_rfl p.levels_pos
  have hprivate : (coordinates p).x i + 4 ∈ pageColumns l (coordinates p) .lower :=
    hcol _ (by simp [specialColumns])
  have hd := readDepth_add_lt_D p 1
  have hn := readDepth_add_lt_D p 2
  change (coordinates p).depth 1 + 64 < p.D at hd
  change (coordinates p).depth 2 + 64 < p.D at hn
  dsimp only [gateFixedSegments]
  simp only [List.append_assoc]
  apply (List.forall_mem_append (p := PageSegment l p)).mpr
  constructor
  · intro s hs
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    refine vertical_page l p .lower (hcol x ?_) (by omega) (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [specialColumns]
  · apply (List.forall_mem_append (p := PageSegment l p)).mpr
    constructor
    · intro s hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl | rfl | rfl
      · apply vertical_page l p .lower hprivate <;> omega
      · exact horizontal_page l p (row_onSide l p .lower hrows.2)
      · exact vertical_main l p haxis
      · apply vertical_page l p .lower hprivate <;> omega
    · split
      · intro s hs
        obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
        apply vertical_page l p .lower (hcol x hx) <;> omega
      · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem wideFixed_pages (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    PageSegments l p (wideFixed l (coordinates p) side) := by
  apply (List.forall_mem_flatMap (p := PageSegment l p)).mpr
  intro ab _
  dsimp only
  split
  · intro s hs
    obtain ⟨y, hy, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      exact horizontal_page l p (row_onSide l p side hy)
  · exact fun _ h => False.elim (List.not_mem_nil h)

private theorem interiorFixed_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) :
    PageSegments l p (interiorFixed l (coordinates p)) := by
  unfold PageSegments interiorFixed
  simp only [List.forall_mem_append]
  refine ⟨⟨⟨⟨?_, ?_⟩, wideFixed_pages l p .upper⟩, wideFixed_pages l p .lower⟩, ?_⟩
  · exact (List.forall_mem_flatMap (p := PageSegment l p)).mpr
      (fun _ he => endpointFixed_pages l p hl hM he)
  · exact (List.forall_mem_flatMap (p := PageSegment l p)).mpr
      (fun _ hi => gateFixed_pages l p hl hi)
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    exact central_page l p (by change p.D ≤ p.D + 4 ∧ p.D ≤ p.D + 4; omega)

private theorem shiftPoint_pages (l : PortLayout) (p : Scales.Parameters) (guards : List ℕ)
    {s : Segment} (hs : PageSegment l p s) :
    PageSegment l p (shiftPoint guards (streetRows (coordinates p)) s) := by
  unfold shiftPoint
  split
  · rename_i hcond
    exact horizontal_page l p (streetRows_selected l p
      (by simpa only [List.contains_iff_mem] using hcond.2.2))
  · exact hs

private theorem markedInterior_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) :
    PageSegments l p (markedInterior l (coordinates p)) := by
  unfold PageSegments
  dsimp only [markedInterior]
  simp only [List.forall_mem_append]
  refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · intro s hs
    split at hs
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
      exact shiftPoint_pages l p _ (interiorFixed_pages l p hl hM u hu)
    · exact interiorFixed_pages l p hl hM s hs
  · apply (List.forall_mem_flatMap (p := PageSegment l p)).mpr
    intro x _ s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact central_page l p (by dsimp only [coordinates]; omega)
  · intro s hs
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    exact central_page l p (by dsimp only [coordinates]; omega)
  · apply (List.forall_mem_flatMap (p := PageSegment l p)).mpr
    intro i _ s hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact central_page l p (by dsimp only [coordinates]; omega)

private theorem frame_pages (l : PortLayout) (p : Scales.Parameters) :
    PageSegments l p (frame (coordinates p)) := by
  intro s hs
  simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact horizontal_page l p (by simp [selectedRows, coordinates])
  · exact horizontal_page l p (by simp [selectedRows, coordinates])
  · exact vertical_main l p (by simp [mainColumnCoordinates])
  · exact vertical_main l p (by simp [mainColumnCoordinates,
      show (coordinates p).W = p.W from rfl])

private theorem endpoint_signal_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) {e : Endpoint}
    (he : e ∈ endpoints l) : PageSegments l p (endpointSegments (coordinates p) state e) := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hrows := workingRows_level l p hj hm
  intro s hs
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · exact vertical_main l p (main_axis l p (l.endpoints_port_lt hl he))
  · exact horizontal_page l p (row_onSide l p e.side hrows.1)

private theorem triple_signal_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (state : SignalState) {g : Placement} (hg : g ∈ placements l) :
    PageSegments l p (tripleSignal (coordinates p) state g) := by
  cases he : g.gate with
  | none => simp [tripleSignal, he, PageSegments]
  | some kind =>
    have hgate := placement_gate_mem l hg he
    have hi := gate_middle_lt l hl hgate
    have hrows := workingRows_level l p (j := 1) le_rfl p.levels_pos
    intro s hs
    simp only [tripleSignal, he, Option.elim_some, gateSegments,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact horizontal_page l p (row_onSide l p .lower hrows.1)
    · exact horizontal_page l p (row_onSide l p .lower hrows.1)
    · exact vertical_main l p (main_axis l p hi)

private theorem encodedSegments_pages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) :
    PageSegments l p (l.encodedSegments p state) := by
  apply (List.forall_mem_append (p := PageSegment l p)).mpr
  constructor
  · exact (List.forall_mem_append (p := PageSegment l p)).mpr
      ⟨frame_pages l p, markedInterior_pages l p hl hM⟩
  · apply (List.forall_mem_append (p := PageSegment l p)).mpr
    constructor
    · exact (List.forall_mem_flatMap (p := PageSegment l p)).mpr
        (fun _ he => endpoint_signal_pages l p hl hM state he)
    · exact (List.forall_mem_flatMap (p := PageSegment l p)).mpr
        (fun _ hg => triple_signal_pages l p hl state hg)

private theorem frame_onPages (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ Boundary.frame) : OnPages l p (q.1.val, q.2.val) := by
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hq
  cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  · left
    simp [selectedRows, hd]
  · right; left
    have he : q.1.val = p.W := by omega
    simp [mainColumnCoordinates, he]
  · left
    have he : q.2.val = p.H := by omega
    simp [selectedRows, he]
  · right; left
    simp [mainColumnCoordinates, hd]

private theorem encoded_without_central_onPages (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hc : q ∉ l.centralMarkers p) : OnPages l p (q.1.val, q.2.val) := by
  obtain ⟨s, hs, hq'⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases encodedSegments_pages l p hl hM state s hs _ hq' with hpage | hband
  · exact hpage
  · by_cases hf : q ∈ Boundary.frame
    · exact frame_onPages l p hf
    have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) := by
      rcases List.mem_append.mp hs with hfix | hsignal
      · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hfix, hq'⟩
      · have hsig := (SegmentRecipe.mem_pointHoles _ _).mpr ⟨s, hsignal, hq'⟩
        have hg := l.signalSegments_central_gap p state hsig
        dsimp only [CentralBand] at hband
        omega
    exact False.elim (hc (Finset.mem_filter.mpr
      ⟨Finset.mem_sdiff.mpr ⟨hfixed, hf⟩, hband⟩))

/-- The emitted target, with all actual central markers filled, has its actual two-page support. -/
theorem encoded_without_central_page_supported (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    Support.Supported (l.twoPageStreets p hl).support (Blocked.fill s (l.centralMarkers p)) := by
  intro q hq
  have hh : q ∉ s.boxes ∧ q ∉ l.centralMarkers p := by simpa [Blocked.fill] using hq
  change OnPages l p (q.1.val, q.2.val)
  apply encoded_without_central_onPages l p hl hM state
  · rw [← hs]
    exact (mem_holes _).mpr hh.1
  · exact hh.2

/-- Every filled prefix of a genuine successful physical instance has the actual two-page
cut support, derived from the emitted target and permanent central markers. -/
theorem physicalInstance_filled_page_supported_at (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Support.Supported (l.twoPageStreets p hl).support (Blocked.fill u (l.centralMarkers p)) := by
  have hr : Relation.ReflTransGen
      (Blocked.ExcludingStep (l.physicalInstance p hl hM ha initial target).board none
        (l.centralMarkers p)) u t := by
    apply Blocked.excluding_of_invariant (fun {_ _} h => h) hut
    intro v huv hvt
    exact l.physicalInstance_central_excluded p hl hM ha initial target (hsu.trans huv) hvt ht
  have hC := (l.twoPageStreets p hl).relativeClosed.union_blockers
    (l.twoPageStreets_blockers_subset p hl)
  apply (Support.supported_fill_iff _ _ u).mpr
  apply hC.reachable_source hr
  apply (Support.supported_fill_iff _ _ t).mp
  apply l.encoded_without_central_page_supported p hl hM target t
  simp only [PushS.holes, ht]
  change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ = _
  simp

end PortLayout
end PushPuzzle.PushS

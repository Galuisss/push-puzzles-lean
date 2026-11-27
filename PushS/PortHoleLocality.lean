/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWideGeometry
public import PushS.PortAxisClear
import all PushS.PortSegments
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortSignalLocality
import all PushS.PortWideGeometry
import all PushS.PortCentralMargins
import all PushS.PortTwoPageStreets
import all PushS.PortStreetSeparation

/-!
# All hole sources inside a wide page-column gap

Away from the frame, central markers and wide separators, every emitted hole stays
within the last branch length plus three of an actual grid axis of either page.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private def NearPageGrid (l : PortLayout) (p : Scales.Parameters) (side : Side) (r x : ℕ) : Prop :=
  ∃ k, k * p.D ∈ l.pageColumnCoordinates p side ∧ x ≤ k * p.D + r ∧ k * p.D ≤ x + r

private theorem near_grid_mono (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {r t x : ℕ} (h : NearPageGrid l p side r x) (hrt : r ≤ t) : NearPageGrid l p side t x := by
  obtain ⟨k, hk, hx, hx'⟩ := h
  exact ⟨k, hk, by omega, by omega⟩

private theorem axis_span_near (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {i x r : ℕ} (hi : i < l.portCount)
    (hx : p.x i - r ≤ x ∧ x ≤ p.x i + r) : NearPageGrid l p side r x := by
  refine ⟨i + 1, axis_in_pageColumns l p hl side hi, hx.2, ?_⟩
  change p.x i ≤ x + r
  omega

private theorem endpoint_fixed_near (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {e : Endpoint} (he : e ∈ endpoints l) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) :
    NearPageGrid l p side (p.L p.levels + 2) q.1 := by
  have hs := fixed_endpoint_span l p e hq
  have hm := readLength_le_last p e.level
  apply near_grid_mono l p side (axis_span_near l p hl side (l.endpoints_port_lt hl he) hs)
  omega

private theorem gate_fixed_near (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {i : ℕ} (hi : i ∈ centers l) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) i)) :
    NearPageGrid l p side (p.L p.levels + 2) q.1 := by
  obtain ⟨kind, first, hg, he⟩ := center_gate_mem l hi
  have hi' : i < l.portCount := by rw [he]; exact gate_middle_lt l hl hg
  have hs := gate_fixed_span p i hq
  have hL := length_floor p
  apply near_grid_mono l p side (axis_span_near l p hl side hi' (r := 12) (by omega))
  omega

private theorem interior_piece (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {s : Segment} (hs : s ∈ interiorFixed l (coordinates p)) :
    s ∈ wideFixed l (coordinates p) .upper ∨ s ∈ wideFixed l (coordinates p) .lower ∨
      ∀ q, s.Contains q → NearPageGrid l p side (p.L p.levels + 2) q.1 := by
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · right; right
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact fun q hq => endpoint_fixed_near l p hl side he ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
  · right; right
    obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
    exact fun q hq => gate_fixed_near l p hl side hi ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩)
  · exact Or.inl hs
  · exact Or.inr (Or.inl hs)
  · right; right
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hs
    intro q hq
    have he := (point_coordinates hq).1
    obtain ⟨k, hk, hx, hx'⟩ := streetColumn_near_grid l p hl side
      (List.mem_append_right _ hx)
    exact ⟨k, hk, by omega, by omega⟩

private theorem shiftPoint_near (l : PortLayout) (p : Scales.Parameters) (side : Side)
    (guards rows : List ℕ) {s : Segment}
    (hs : ∀ q, s.Contains q → NearPageGrid l p side (p.L p.levels + 2) q.1)
    {q : ℕ × ℕ} (hq : (shiftPoint guards rows s).Contains q) :
    NearPageGrid l p side (p.L p.levels + 3) q.1 := by
  unfold shiftPoint at hq
  split at hq
  · rename_i hcond
    have hself := point_start_contains s hcond.1
    obtain ⟨k, hk, hx, hx'⟩ := hs s.start hself
    have he := (point_coordinates hq).1
    exact ⟨k, hk, by omega, by omega⟩
  · exact near_grid_mono l p side (hs q hq) (by omega)

private theorem marked_shifted_piece (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) (rounded : Bool) {s : Segment}
    (hs : s ∈ if rounded then
      (interiorFixed l (coordinates p)).map
        (shiftPoint (guardColumns l (coordinates p) (frame (coordinates p) ++ interiorFixed l (coordinates p)))
          (streetRows (coordinates p))) else interiorFixed l (coordinates p))
    (hround : rounded = (guardColumns l (coordinates p) (frame (coordinates p) ++ interiorFixed l (coordinates p))).any
      (fun x => (guardColumns l (coordinates p) (frame (coordinates p) ++ interiorFixed l (coordinates p))).contains (x + 1)))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : s.Contains (q.1.val, q.2.val)) :
    q ∈ l.wideSeparatorHoles p ∨ NearPageGrid l p side (p.L p.levels + 3) q.1.val := by
  cases hr : rounded
  · simp only [hr, Bool.false_eq_true, ite_false] at hs
    rcases interior_piece l p hl side hs with hw | hw | hlocal
    · left
      apply (SegmentRecipe.mem_holes _ q).mpr
      refine ⟨s, List.mem_append_left _ ?_, hq⟩
      dsimp only [physicalWideSegments]
      rw [← hround, hr]
      exact hw
    · left
      apply (SegmentRecipe.mem_holes _ q).mpr
      refine ⟨s, List.mem_append_right _ ?_, hq⟩
      dsimp only [physicalWideSegments]
      rw [← hround, hr]
      exact hw
    · exact Or.inr (near_grid_mono l p side (hlocal _ hq) (by omega))
  · simp only [hr, ite_true] at hs
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
    rcases interior_piece l p hl side hu with hw | hw | hlocal
    · left
      apply (SegmentRecipe.mem_holes _ q).mpr
      refine ⟨_, List.mem_append_left _ ?_, hq⟩
      dsimp only [physicalWideSegments]
      rw [← hround, hr]
      exact List.mem_map.mpr ⟨u, hw, rfl⟩
    · left
      apply (SegmentRecipe.mem_holes _ q).mpr
      refine ⟨_, List.mem_append_right _ ?_, hq⟩
      dsimp only [physicalWideSegments]
      rw [← hround, hr]
      exact List.mem_map.mpr ⟨u, hw, rfl⟩
    · exact Or.inr (shiftPoint_near l p side _ _ hlocal hq)

private theorem marked_piece (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {s : Segment} (hs : s ∈ markedInterior l (coordinates p))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : s.Contains (q.1.val, q.2.val)) (hf : q ∉ Boundary.frame) :
    q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p ∨
      NearPageGrid l p side (p.L p.levels + 3) q.1.val := by
  have hfixed : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) :=
    (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs, hq⟩
  have hcentral (hy : p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4) : q ∈ l.centralMarkers p :=
    Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hfixed, hf⟩, hy⟩
  dsimp only [markedInterior] at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs
  · exact Or.inr (marked_shifted_piece l p hl side _ hs rfl hq)
  · obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals
      have hp := (point_coordinates hq).2
      apply Or.inl (hcentral ?_)
      dsimp only [coordinates] at hp
      omega
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := (point_coordinates hq).2
    apply Or.inl (hcentral ?_)
    dsimp only [coordinates] at hp
    omega
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals
      have hp := (point_coordinates hq).2
      apply Or.inl (hcentral ?_)
      dsimp only [coordinates] at hp
      omega

private theorem signal_near (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) (state : SignalState) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.signalSegments p state)) :
    NearPageGrid l p side (p.L p.levels + 3) q.1 := by
  obtain ⟨i, hi, hx⟩ := l.signalSegments_near_axis p hl state hq
  have hL := length_floor p
  apply near_grid_mono l p side (axis_span_near l p hl side hi (r := 12) ?_) (by omega)
  simp only [Nat.dist] at hx
  omega

private theorem near_grid_dist (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {r x : ℕ} (h : NearPageGrid l p side r x) :
    ∃ k, k * p.D ∈ l.pageColumnCoordinates p side ∧ Nat.dist x (k * p.D) ≤ r := by
  obtain ⟨k, hk, hx, hx'⟩ := h
  exact ⟨k, hk, by simp only [Nat.dist]; omega⟩

/-- Every actual interior hole comes from a central marker, a physical wide separator, or
the bounded neighbourhood of a grid axis present on either selected page. -/
theorem encodedSegments_hole_locality (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) (state : SignalState) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    (hf : q ∉ Boundary.frame) :
    q ∈ l.centralMarkers p ∨ q ∈ l.wideSeparatorHoles p ∨
      ∃ k, k * p.D ∈ l.pageColumnCoordinates p side ∧
        Nat.dist q.1.val (k * p.D) ≤ p.L p.levels + 3 := by
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  rcases List.mem_append.mp hs with hfixed | hsignal
  · rcases List.mem_append.mp hfixed with hframe | hmarked
    · exact False.elim (hf (frame_contains (coordinates p) q ⟨s, hframe, hq⟩))
    · rcases marked_piece l p hl side hmarked hq hf with hc | hw | hnear
      · exact Or.inl hc
      · exact Or.inr (Or.inl hw)
      · exact Or.inr (Or.inr (near_grid_dist l p side hnear))
  · exact Or.inr (Or.inr (near_grid_dist l p side (signal_near l p hl side state
      ((mem_pointHoles _ _).mpr ⟨s, hsignal, hq⟩))))

/-- The actual encoded board is full away from central and wide holes in the middle of any
gap whose page columns all lie beyond the local branch radius. -/
theorem encodedSegments_far_from_page_columns_full (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) (state : SignalState) (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state))
    {q : Cell (p.W + 1) (p.H + 1)} (hf : q ∉ Boundary.frame) (hc : q ∉ l.centralMarkers p)
    (hw : q ∉ l.wideSeparatorHoles p)
    (hx : ∀ x ∈ l.pageColumnCoordinates p side, p.L p.levels + 3 < Nat.dist q.1.val x) :
    q ∈ s.boxes := by
  by_contra hq
  have hh : q ∈ PushS.holes s := (mem_holes _).mpr hq
  rw [hs] at hh
  rcases l.encodedSegments_hole_locality p hl side state hh hf with hc' | hw' | ⟨k, hk, hg⟩
  · exact hc hc'
  · exact hw hw'
  · have hfar := hx _ hk
    omega

end PushPuzzle.PushS.PortLayout

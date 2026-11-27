/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortCentralMargins
public import PushS.PortInstance

/-!
# Permanent central holes of the actual marked storage instance

The complete fixed recipe determines its central markers directly. The exact storage target
requires every marker to be empty, and the geometric budget excludes every visit to it.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- The actual non-frame fixed holes in the central acceptance band. -/
@[expose] def centralMarkers (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.fixedSegments p) \ Boundary.frame).filter
    fun q => p.D ≤ q.2.val + 4 ∧ q.2.val ≤ p.D + 4

/-- Every central marker is a hole of every actual physical signal encoding. -/
theorem centralMarkers_subset_encoded (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    l.centralMarkers p ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨hq, _⟩ := Finset.mem_filter.mp hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp (Finset.mem_sdiff.mp hq).1
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hq⟩

/-- Every emitted central marker exceeds the complete physical interior-hole budget. -/
theorem centralMarkers_far (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (state : SignalState) (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)) :
    ∀ q ∈ l.centralMarkers p, Distant.Far s q := by
  intro q hq
  obtain ⟨hq, hy, hy'⟩ := Finset.mem_filter.mp hq
  obtain ⟨hq, hf⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨hx, hx'⟩ := l.fixedSegments_interior_column_margins p hl ha hq hf
  exact l.far_of_central_margins p hl ha state s hs q (by omega) (by omega) hy hy'

/-- Every frame cell is a hole of every actual physical encoding. -/
theorem encodedSegments_frame_subset (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    Boundary.frame ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hq
  have hh : SegmentRecipe.holeTest (l.fixedSegments p, q.1.val, q.2.val) = true := by
    cases d with
    | north =>
      exact l.horizontal_frame_empty p (Or.inl (by simpa [Boundary.edge] using hd)) (by omega)
    | south =>
      exact l.horizontal_frame_empty p (Or.inr (by simpa [Boundary.edge] using hd)) (by omega)
    | west =>
      exact l.vertical_frame_empty p (Or.inl (by simpa [Boundary.edge] using hd)) (by omega)
    | east =>
      exact l.vertical_frame_empty p (Or.inr (by simpa [Boundary.edge] using hd)) (by omega)
  simpa only [SegmentRecipe.holes, Finset.mem_filter, Finset.mem_univ, true_and] using
    (l.holeTest_encodedSegments p state _).mpr (Or.inl hh)

/-- Along any actual successful physical encoding, the central markers stay empty and unvisited. -/
theorem centralMarkers_excluded_at (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (initial target : SignalState)
    {B : Board (p.W + 1) (p.H + 1)} {cap : Option ℕ}
    {s u t : State (p.W + 1) (p.H + 1)} (hsu : Reachable B cap s u) (hut : Reachable B cap u t)
    (hp : s.player ∈ Boundary.frame)
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))
    (ht : PushS.holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target)) :
    Blocked.Excluded (l.centralMarkers p) u := by
  have hf : Disjoint t.boxes Boundary.frame := by
    apply Finset.disjoint_left.mpr
    intro q hbox hframe
    have hh := encodedSegments_frame_subset l p target hframe
    rw [← ht] at hh
    exact (mem_holes _).mp hh hbox
  apply Distant.excluded_at hsu hut hp hf (l.centralMarkers_far p hl ha initial s hs)
  rw [ht]
  exact l.centralMarkers_subset_encoded p target

/-- The central markers are permanent on every solution prefix of the constructed wall-free
storage instance, with no additional geometric or inventory assumptions. -/
theorem physicalInstance_central_excluded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Blocked.Excluded (l.centralMarkers p) u := by
  apply l.centralMarkers_excluded_at p hl ha initial target hsu hut
  · apply (Boundary.mem_frame _).mpr
    exact ⟨.north, by simp [Boundary.edge, physicalInstance, SegmentRecipe.toInstance,
      Instance.ofHoles, Instance.ofState, HoleState.toState, segmentRecipe]⟩
  · change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))ᶜᶜ = _
    simp
  · simp only [PushS.holes, ht]
    change (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target))ᶜᶜ = _
    simp

/-- Every solution of the constructed instance runs unchanged with its central markers blocked. -/
theorem physicalInstance_central_block (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Reachable (Blocked.block (l.physicalInstance p hl hM ha initial target).board
      (l.centralMarkers p)) none (l.physicalInstance p hl hM ha initial target).initial t :=
  Blocked.reachable_block_of_invariant (fun {_ _} h => h) hr
    (fun _ hsu hut => l.physicalInstance_central_excluded p hl hM ha initial target hsu hut ht)

/-- Every segment of a successful physical play survives filling the central markers. -/
theorem physicalInstance_central_fill_between (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {u v t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (huv : Reachable (l.physicalInstance p hl hM ha initial target).board none u v)
    (hvt : Reachable (l.physicalInstance p hl hM ha initial target).board none v t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill u (l.centralMarkers p)) (Blocked.fill v (l.centralMarkers p)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) huv
    (fun _ hux hxv => l.physicalInstance_central_excluded p hl hM ha initial target
      (hsu.trans hux) (hxv.trans hvt) ht)
  rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
  exact Finset.disjoint_empty_right _

/-- Filling all permanent central markers with ordinary boxes preserves the successful play
on the same wall-free board. -/
theorem physicalInstance_central_fill (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill (l.physicalInstance p hl hM ha initial target).initial (l.centralMarkers p))
      (Blocked.fill t (l.centralMarkers p)) :=
  l.physicalInstance_central_fill_between p hl hM ha initial target .refl hr .refl ht

end PushPuzzle.PushS.PortLayout

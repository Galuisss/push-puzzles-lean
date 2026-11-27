/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWideGeometry
public import PushS.PortCentralStrip
public import PushS.StreetExits
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual wide separator holes are permanent and unvisited on every successful storage play. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

private theorem wide_not_central (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) : q ∉ l.centralMarkers p := by
  have hrow := l.workingRowSet_central_gap p (l.wideSeparatorHoles_working_row p hq)
  have hY := readDepth_add_lt_D p p.levels
  rw [readDepth_eq p p.levels_pos le_rfl] at hY
  have hH : p.H = 2 * p.D := rfl
  intro hc
  obtain ⟨_, hy, hy'⟩ := Finset.mem_filter.mp hc
  omega

private theorem wide_subset_encoded (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    l.wideSeparatorHoles p ⊆ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  intro q hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp (l.wideSeparatorHoles_subset_fixed p hq)
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hq⟩

private theorem filled_interior_budget (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (initial : SignalState) (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial)) :
    (holes (Blocked.fill s (l.centralMarkers p)) \ Boundary.frame).card ≤ 2 * p.b p.levels := by
  have hb := l.encodedSegments_interior_card_le p hl ha initial
  rw [← hs] at hb
  apply le_trans (Finset.card_le_card ?_) hb
  intro q hq
  obtain ⟨hq, hf⟩ := Finset.mem_sdiff.mp hq
  refine Finset.mem_sdiff.mpr ⟨(mem_holes _).mpr ?_, hf⟩
  intro hbox
  exact (mem_holes _).mp hq (Finset.mem_union_left _ hbox)

private theorem wide_far_exits (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) (initial : SignalState) (s : State (p.W + 1) (p.H + 1))
    (hs : PushS.holes s = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p initial))
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) :
    ∀ a ∈ Support.frameExits (l.streetColumnSet p) (l.workingRowSet p),
      (holes (Blocked.fill s (l.centralMarkers p)) \ Boundary.frame).card < distance a q := by
  have hb := filled_interior_budget l p hl ha initial s hs
  have hg := l.wideSeparatorHoles_street_gap p hl hq
  have hleft := hg (⟨0, by omega⟩ : Fin (p.W + 1)) (by
    change 0 ∈ streetColumns l (coordinates p); simp [streetColumns])
  have hright := hg (⟨p.W, by omega⟩ : Fin (p.W + 1)) (by
    change p.W ∈ streetColumns l (coordinates p); simp [streetColumns, coordinates])
  apply Support.frameExits_far_of_column_gap
  · simp only [Nat.dist] at hleft
    omega
  · simp only [Nat.dist] at hright
    have := q.1.isLt
    omega
  · intro x hx
    have hd := hg x hx
    simp only [Nat.dist] at hd ⊢
    omega

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

private theorem filled_final_frame {t : State (p.W + 1) (p.H + 1)}
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Disjoint (Blocked.fill t (l.centralMarkers p)).boxes Boundary.frame := by
  have hholes : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
    change t.boxesᶜ = _
    rw [ht]
    exact l.physicalInstance_goal_holes p hl hM ha initial target
  apply Finset.disjoint_left.mpr
  intro q hbox hf
  rcases Finset.mem_union.mp hbox with hbox | hcentral
  · have hh := l.encodedSegments_frame_subset p target hf
    rw [← hholes] at hh
    exact (mem_holes _).mp hh hbox
  · exact (Finset.mem_sdiff.mp (Finset.mem_filter.mp hcentral).1).2 hf

/-- Every actual rounded wide separator remains empty and unvisited at every solution prefix. -/
theorem physicalInstance_wide_excluded_at {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Blocked.Excluded (l.wideSeparatorHoles p) u := by
  have hsu' := l.physicalInstance_central_fill_between p hl hM ha initial target .refl hsu hut ht
  have hut' := l.physicalInstance_central_fill_between p hl hM ha initial target hsu hut .refl ht
  have hp := l.physicalInstance_initial_frame p hl hM ha initial target
  have hf := filled_final_frame l p hl hM ha initial target ht
  have hU := l.physicalInstance_filled_supported_at p hl hM ha initial target hsu hut ht
  have hT := l.physicalInstance_filled_supported_at p hl hM ha initial target (hsu.trans hut) .refl ht
  have hfar (q : Cell (p.W + 1) (p.H + 1)) (hq : q ∈ l.wideSeparatorHoles p) :=
    wide_far_exits l p hl ha initial _ (l.physicalInstance_initial_holes p hl hM ha initial target) hq
  have hholes : holes t = SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p target) := by
    change t.boxesᶜ = _
    rw [ht]
    exact l.physicalInstance_goal_holes p hl hM ha initial target
  constructor
  · intro q hq
    have hfinal : q ∈ holes (Blocked.fill t (l.centralMarkers p)) := by
      apply (mem_holes _).mpr
      intro hb
      rcases Finset.mem_union.mp hb with hb | hc
      · have hh := wide_subset_encoded l p target hq
        rw [← hholes] at hh
        exact (mem_holes _).mp hh hb
      · exact wide_not_central l p hq hc
    have hhole := Support.hole_at_of_frame_exits (l.streetColumnSet_separated p)
      (l.workingRowSet_separated p) hsu' hut' hp hf hT
      (l.wideSeparatorHoles_off_frame p hl hq) (hfar _ hq) hfinal
    exact (mem_holes _).mpr (fun hb => (mem_holes _).mp hhole (Finset.mem_union_left _ hb))
  · intro hq
    have hne := Support.player_ne_of_frame_exits (l.streetColumnSet_separated p)
      (l.workingRowSet_separated p) hsu' hp (Boundary.reachable_frame_empty hut' hf) hU
      (l.wideSeparatorHoles_off_frame p hl hq) (hfar _ hq)
    exact hne rfl

/-- Filling the actual wide separators with ordinary boxes preserves every successful move. -/
theorem physicalInstance_wide_fill {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Reachable (l.physicalInstance p hl hM ha initial target).board none
      (Blocked.fill (l.physicalInstance p hl hM ha initial target).initial (l.wideSeparatorHoles p))
      (Blocked.fill t (l.wideSeparatorHoles p)) := by
  apply Blocked.reachable_fill_of_invariant (fun {_ _} h => h) hr
    (fun _ hsu hut => l.physicalInstance_wide_excluded_at p hl hM ha initial target hsu hut ht)
  rw [(l.physicalInstance p hl hM ha initial target).walls_empty]
  exact Finset.disjoint_empty_right _

end Solution
end PushPuzzle.PushS.PortLayout

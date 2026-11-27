/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortPointBudget
import all PushS.PortPointBudget
import all PushS.PortWalkBudget
import all PushS.PortHoleBudget
import all PushS.PortSegments

/-! The actual outside-walk hole inventory at each reader level. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

private theorem endpoint_long_partition (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    {e : Endpoint} (he : e ∈ l.endpoints) {s : Segment}
    (hs : s ∈ (endpointFixedSegments l (coordinates p) e).take 3) :
    s ∈ l.readerWalkSegments p j ∨ s ∈ l.readerResidualSegments p j := by
  let ss := endpointFixedSegments l (coordinates p) e
  obtain ⟨k, hk, hread⟩ := List.mem_iff_getElem.mp hs
  have hk3 : k < 3 := by rw [List.length_take] at hk; omega
  have hzip : (s, k) ∈ (ss.take 3).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?, List.getElem?_eq_getElem hk]
    exact congrArg some hread
  by_cases hsel : if k = 1 then j < e.level else j ≤ e.level
  · left
    exact List.mem_flatMap.mpr ⟨e, he, List.mem_filterMap.mpr ⟨(s, k), hzip, by simp [hsel]⟩⟩
  · right
    have hread' := List.mem_zipIdx_iff_getElem?.mp hzip
    rw [List.getElem?_take_of_lt hk3] at hread'
    have hslice : s ∈ (ss.drop k).take 1 := by
      rw [List.take_one, List.head?_drop, hread']
      simp
    simp only [readerResidualSegments, List.mem_append, or_assoc]
    rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · left
      have hl : e.level < j := by simpa using hsel
      exact List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hl]⟩,
        by simpa only [List.drop_zero] using hslice⟩
    · right; left
      have hl : e.level ≤ j := by simpa using hsel
      exact List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hl]⟩, hslice⟩
    · right; right; left
      have hl : e.level < j := by simpa using hsel
      exact List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simp [hl]⟩, hslice⟩

private theorem shift_nonpoint_mem (ss : List Segment) (guards rows : List ℕ) {s : Segment}
    (hs : s ∈ ss.map (shiftPoint guards rows)) (hn : s.start ≠ s.finish) : s ∈ ss := by
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
  unfold shiftPoint at hn ⊢
  split_ifs at hn ⊢
  · exact False.elim (hn rfl)
  · exact ht

private theorem marked_nonpoint_base (l : PortLayout) (p : Scales.Parameters) {s : Segment}
    (hs : s ∈ markedInterior l (coordinates p)) (hn : s.start ≠ s.finish) :
    s ∈ interiorFixed l (coordinates p) := by
  unfold markedInterior at hs
  extract_lets base guards shifted aux marked at hs
  change s ∈ ((shifted ++ _) ++ _) ++ _ at hs
  simp only [List.mem_append, or_assoc] at hs
  rcases hs with hshift | haux | hguard | hcore
  · dsimp only [shifted] at hshift
    split at hshift
    · exact shift_nonpoint_mem base _ _ hshift hn
    · exact hshift
  · obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp haux
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact False.elim (hn rfl)
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hguard
    exact False.elim (hn rfl)
  · obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hcore
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl <;> exact False.elim (hn rfl)

private theorem gate_nonpoint_tail_private (p : Scales.Parameters) (i : ℕ) {s : Segment}
    (hs : s ∈ (gateFixedSegments (coordinates p) i).drop 4) (hn : s.start ≠ s.finish) :
    s ∈ ((gateFixedSegments (coordinates p) i).drop 5).take 1 := by
  dsimp only [gateFixedSegments] at hs ⊢
  simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
    List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
  rcases hs with rfl | hs | rfl | rfl | hs
  · exact False.elim (hn rfl)
  · exact hs
  · exact False.elim (hn rfl)
  · exact False.elim (hn rfl)
  · split at hs
    · obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs
      exact False.elim (hn rfl)
    · cases hs

private theorem wide_points (l : PortLayout) (p : Coordinates) (side : Side) {s : Segment}
    (hs : s ∈ wideFixed l p side) : s.start = s.finish := by
  obtain ⟨ab, _, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · obtain ⟨v, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · cases hs; rfl
  · cases hs

private theorem base_nonpoint_partition (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    (state : SignalState) {s : Segment} (hs : s ∈ interiorFixed l (coordinates p))
    (hn : s.start ≠ s.finish) :
    s ∈ l.readerWalkSegments p j ∨ s ∈ l.readerResidualSegments p j ∨ s ∈ l.readerSmallSegments p state := by
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hend | hgate | hu | hd | haux
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hend
    rw [← List.take_append_drop 3 (endpointFixedSegments l (coordinates p) e), List.mem_append] at hs
    rcases hs with hlong | htail
    · exact (endpoint_long_partition l p j he hlong).elim Or.inl (fun h => Or.inr (Or.inl h))
    · exact False.elim (hn (endpoint_tail_points l p e htail))
  · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hgate
    rw [← List.take_append_drop 4 (gateFixedSegments (coordinates p) i), List.mem_append] at hs
    rcases hs with hlong | htail
    · right; left
      simp only [readerResidualSegments, List.mem_append, or_assoc]
      right; right; right
      exact List.mem_flatMap.mpr ⟨i, hi, hlong⟩
    · right; right
      simp only [readerSmallSegments, List.mem_append, or_assoc]
      right; left
      exact List.mem_flatMap.mpr ⟨i, hi, gate_nonpoint_tail_private p i htail hn⟩
  · exact False.elim (hn (wide_points l (coordinates p) .upper hu))
  · exact False.elim (hn (wide_points l (coordinates p) .lower hd))
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp haux
    exact False.elim (hn rfl)

/-- Every actual hole outside the removed public walks belongs to residual or small stock. -/
theorem encodedSegments_outside_readerWalk_subset (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (j : ℕ) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.readerWalkHoles p j ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1)
        (l.readerResidualSegments p j ++ l.readerSmallSegments p state) := by
  intro q hq
  obtain ⟨hq, hout⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have residual (hs : s ∈ l.readerResidualSegments p j) : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.readerResidualSegments p j ++ l.readerSmallSegments p state) :=
    (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_left _ hs, hcontains⟩
  have small (hs : s ∈ l.readerSmallSegments p state) : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1)
      (l.readerResidualSegments p j ++ l.readerSmallSegments p state) :=
    (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs, hcontains⟩
  rcases List.mem_append.mp hs with hfixed | hsignal
  · rcases List.mem_append.mp hfixed with hframe | hmarked
    · exact False.elim (hout (Finset.mem_union_left _ (frame_contains (coordinates p) q ⟨s, hframe, hcontains⟩)))
    · by_cases hn : s.start = s.finish
      · apply small
        simp only [readerSmallSegments, List.mem_append, or_assoc]
        left
        exact List.mem_filter.mpr ⟨hmarked, by simp [hn]⟩
      · have hbase := marked_nonpoint_base l p hmarked hn
        rcases base_nonpoint_partition l p j state hbase hn with hwalk | hresidual | hsmall
        · exact False.elim (hout (Finset.mem_union_right _
            ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hwalk, hcontains⟩)))
        · exact residual hresidual
        · exact small hsmall
  · exact small (List.mem_append_right _ hsignal)

private theorem finite_holes_card_le_trace (w h : ℕ) (ss : List Segment) :
    (SegmentRecipe.holes w h ss).card ≤ traceLength ss := by
  have hc : (SegmentRecipe.holes w h ss).card ≤ (pointHoles ss).card := by
    apply Finset.card_le_card_of_injOn (fun q : Cell w h => (q.1.val, q.2.val))
    · intro q hq
      exact (mem_pointHoles _ _).mpr ((SegmentRecipe.mem_holes _ q).mp hq)
    · intro q _ r _ heq
      exact Prod.ext (Fin.ext (congrArg Prod.fst heq)) (Fin.ext (congrArg Prod.snd heq))
  exact hc.trans (pointHoles_card_le ss)

/-- The actual encoded holes outside the reader walks fit the geometric reader budget. -/
theorem encodedSegments_outside_readerWalk_card_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {j : ℕ} (hj : 1 ≤ j) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.readerWalkHoles p j).card ≤ p.K j := by
  have hc := Finset.card_le_card (l.encodedSegments_outside_readerWalk_subset p state j)
  have ht := finite_holes_card_le_trace (p.W + 1) (p.H + 1)
    (l.readerResidualSegments p j ++ l.readerSmallSegments p state)
  have hr := l.readerResidualSegments_trace_length_le p hl hM ha hj
  have hs := l.readerSmallSegments_trace_length_le p hl hM ha state
  change traceLength _ ≤ _ at hr hs
  rw [trace_append] at ht
  unfold Scales.Parameters.K
  omega

end PushPuzzle.PushS.PortLayout

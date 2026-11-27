/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortReaderBudget
import all PushS.PortReaderBudget
import all PushS.PortWalkBudget
import all PushS.PortHoleBudget
import all PushS.PortSegments

/-! The actual hole budget after clearing all public walks strictly deeper than a level. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- All three public endpoint segments, uniformly selected strictly below the current level. -/
def deeperWalkSegments (l : PortLayout) (p : Scales.Parameters) (j : ℕ) : List Segment :=
  (l.endpoints.filter fun e => decide (j < e.level)).flatMap fun e =>
    (endpointFixedSegments l (coordinates p) e).take 3

/-- The actual frame together with all deeper f/r walks and long public branches. -/
@[expose] def deeperWalkHoles (l : PortLayout) (p : Scales.Parameters) (j : ℕ) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Boundary.frame ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.deeperWalkSegments p j)

private def levelSegments (l : PortLayout) (p : Scales.Parameters) (j : ℕ) : List Segment :=
  (l.endpoints.filter fun e => decide (e.level = j)).flatMap fun e =>
    (endpointFixedSegments l (coordinates p) e).take 3

private theorem outside_deeper_subset (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (j : ℕ) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.deeperWalkHoles p j ⊆
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.readerWalkHoles p j) ∪
        SegmentRecipe.holes (p.W + 1) (p.H + 1) (levelSegments l p j) := by
  intro q hq
  obtain ⟨hencoded, hdeep⟩ := Finset.mem_sdiff.mp hq
  by_cases hreader : q ∈ l.readerWalkHoles p j
  · apply Finset.mem_union_right
    rcases Finset.mem_union.mp hreader with hframe | hwalk
    · exact False.elim (hdeep (Finset.mem_union_left _ hframe))
    obtain ⟨s, hs, hcontains⟩ := (SegmentRecipe.mem_holes _ q).mp hwalk
    obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨⟨seg, k⟩, hzip, hselected⟩ := List.mem_filterMap.mp hs
    dsimp only at hselected
    have heq : seg = s := by split_ifs at hselected <;> exact Option.some.inj hselected
    subst s
    have hlev : j ≤ e.level := by split_ifs at hselected <;> omega
    have hbase := List.fst_mem_of_mem_zipIdx hzip
    by_cases hdeeper : j < e.level
    · apply False.elim
      apply hdeep
      apply Finset.mem_union_right
      apply (SegmentRecipe.mem_holes _ q).mpr
      exact ⟨seg, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simpa using hdeeper⟩, hbase⟩,
        hcontains⟩
    · have helevel : e.level = j := by omega
      apply (SegmentRecipe.mem_holes _ q).mpr
      exact ⟨seg, List.mem_flatMap.mpr ⟨e, List.mem_filter.mpr ⟨he, by simpa using helevel⟩, hbase⟩,
        hcontains⟩
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mpr ⟨hencoded, hreader⟩)

private theorem level_trace_le (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (j : ℕ) :
    traceLength (levelSegments l p j) ≤ 4 * p.axes * (p.Y j + 2) + 2 * p.axes * p.L j := by
  have hb : traceLength (levelSegments l p j) ≤ 2 * l.portCount * (2 * (p.Y j + 2) + p.L j) := by
    apply endpoint_filtered_trace l hl
    intro e he hlev
    have helevel : e.level ≤ j := le_of_eq (of_decide_eq_true hlev)
    obtain ⟨hf, hr, hb⟩ := endpoint_base_trace l p hl hM he
    have hd := readDepth_le_level p helevel
    have hL := readLength_le_level p helevel
    have hsplit : traceLength ((endpointFixedSegments l (coordinates p) e).take 3) =
        traceLength ((endpointFixedSegments l (coordinates p) e).take 1) +
        traceLength (((endpointFixedSegments l (coordinates p) e).drop 1).take 1) +
        traceLength (((endpointFixedSegments l (coordinates p) e).drop 2).take 1) := by
      dsimp only [endpointFixedSegments]
      simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
        List.drop_succ_cons, List.drop_zero, trace_cons, trace_nil, Nat.add_zero]
      omega
    rw [hsplit]
    omega
  have hm := Nat.mul_le_mul_right (2 * (p.Y j + 2) + p.L j) (Nat.mul_le_mul_left 2 ha)
  nlinarith

/-- Clearing the actual deeper public walks leaves at most the interlevel budget `b j` holes. -/
theorem encodedSegments_outside_deeperWalk_card_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) {j : ℕ} (hj : 1 ≤ j) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.deeperWalkHoles p j).card ≤ p.b j := by
  have hc := Finset.card_le_card (outside_deeper_subset l p state j)
  have hu := Finset.card_union_le
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.readerWalkHoles p j)
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (levelSegments l p j))
  have hr := l.encodedSegments_outside_readerWalk_card_le p hl hM ha state hj
  have ht := finite_holes_card_le_trace (p.W + 1) (p.H + 1) (levelSegments l p j)
  have hb := level_trace_le l p hl hM ha j
  have hprev := L_le p (show j - 1 ≤ j by omega)
  have hp := Nat.mul_le_mul_left (2 * p.axes) hprev
  unfold Scales.Parameters.K at hr
  unfold Scales.Parameters.b
  nlinarith

end PushPuzzle.PushS.PortLayout

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

/-! Clearing all actual public walks leaves only the bounded small-hole stock. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction SegmentRecipe

/-- Every ordinary f/r walk and long branch, and every gate's four public long columns. -/
@[expose] def allPublicWalkSegments (l : PortLayout) (p : Scales.Parameters) : List Segment :=
  l.endpoints.flatMap (fun e => (endpointFixedSegments l (coordinates p) e).take 3) ++
    l.gateCenterCoordinates.flatMap (fun i => (gateFixedSegments (coordinates p) i).take 4)

/-- The actual frame together with every emitted public walk. -/
@[expose] def allPublicWalkHoles (l : PortLayout) (p : Scales.Parameters) :
    Finset (Cell (p.W + 1) (p.H + 1)) :=
  Boundary.frame ∪ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.allPublicWalkSegments p)

private theorem ordinary_public_mem (l : PortLayout) (p : Scales.Parameters)
    {e : Endpoint} (he : e ∈ l.endpoints) {s : Segment}
    (hs : s ∈ (endpointFixedSegments l (coordinates p) e).take 3) : s ∈ l.allPublicWalkSegments p :=
  List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hs⟩)

private theorem reader_walk_public (l : PortLayout) (p : Scales.Parameters) (j : ℕ)
    {s : Segment} (hs : s ∈ l.readerWalkSegments p j) : s ∈ l.allPublicWalkSegments p := by
  obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨⟨t, k⟩, hzip, hselected⟩ := List.mem_filterMap.mp hs
  dsimp only at hselected
  have heq : t = s := by split_ifs at hselected <;> exact Option.some.inj hselected
  subst s
  exact ordinary_public_mem l p he (List.fst_mem_of_mem_zipIdx hzip)

private theorem residual_zero_public (l : PortLayout) (p : Scales.Parameters)
    {s : Segment} (hs : s ∈ l.readerResidualSegments p 0) : s ∈ l.allPublicWalkSegments p := by
  have hnil : l.endpoints.filter (fun e => decide (e.level < 0)) = [] := by simp
  simp only [readerResidualSegments, hnil, List.flatMap_nil, List.nil_append, List.append_nil] at hs
  rcases List.mem_append.mp hs with hr | hg
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hr
    apply ordinary_public_mem l p (List.mem_filter.mp he).1
    dsimp only [endpointFixedSegments] at hs ⊢
    simp only [List.cons_append, List.nil_append, List.drop_succ_cons, List.drop_zero,
      List.take_succ_cons, List.take_zero, List.mem_cons, List.not_mem_nil, or_false] at hs ⊢
    exact Or.inr (Or.inl hs)
  · exact List.mem_append_right _ hg

private theorem reader_zero_subset (l : PortLayout) (p : Scales.Parameters) :
    l.readerWalkHoles p 0 ⊆ l.allPublicWalkHoles p := by
  intro q hq
  rcases Finset.mem_union.mp hq with hf | hw
  · exact Finset.mem_union_left _ hf
  · obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hw
    exact Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr
      ⟨s, reader_walk_public l p 0 hs, hq⟩)

/-- Every actual hole outside all public walks belongs to the emitted small-hole stock. -/
theorem encodedSegments_outside_allPublicWalk_subset (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) :
    SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.allPublicWalkHoles p ⊆
      SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.readerSmallSegments p state) := by
  intro q hq
  obtain ⟨hencoded, hout⟩ := Finset.mem_sdiff.mp hq
  have hreader : q ∉ l.readerWalkHoles p 0 := fun h => hout (reader_zero_subset l p h)
  have hcover := l.encodedSegments_outside_readerWalk_subset p state 0
    (Finset.mem_sdiff.mpr ⟨hencoded, hreader⟩)
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_holes _ q).mp hcover
  rcases List.mem_append.mp hs with hr | hsmall
  · exact False.elim (hout (Finset.mem_union_right _ ((SegmentRecipe.mem_holes _ q).mpr
      ⟨s, residual_zero_public l p hr, hq⟩)))
  · exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, hsmall, hq⟩

/-- The complete emitted holes outside the actual public walks fit the final budget `Q`. -/
theorem encodedSegments_outside_allPublicWalk_card_le (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (state : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) \ l.allPublicWalkHoles p).card ≤ p.Q := by
  have hc := Finset.card_le_card (l.encodedSegments_outside_allPublicWalk_subset p state)
  have ht := finite_holes_card_le_trace (p.W + 1) (p.H + 1) (l.readerSmallSegments p state)
  have hs := l.readerSmallSegments_trace_length_le p hl hM ha state
  exact (hc.trans ht).trans hs

end PushPuzzle.PushS.PortLayout

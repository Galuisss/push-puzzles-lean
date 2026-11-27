/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortSegmentBounds
import Mathlib.Data.Finset.Card

/-!
# Exact cardinalities of the actual finite hole unions

The physical segment bounds identify the emitted finite-cell holes with the full union
of their integer traces. The complete recipe then has the exact fixed/signal union
cardinality, accounting for their actual intersection.

## Main results

* `PortLayout.encodedSegments_holes_card`: finite-cell holes count the entire physical union.
* `PortLayout.encodedSegments_holes_card_union`: exact fixed/signal cardinality accounting.
-/

public section

namespace PushPuzzle.PushS


open PushFS PushFS.Reduction

namespace SegmentRecipe

/-- The finite union of the integer traces of a segment list. -/
@[expose] def pointHoles (ss : List Segment) : Finset (ℕ × ℕ) :=
  (ss.flatMap Segment.cells).toFinset

/-- Integer-trace membership uses precisely the existing segment semantics. -/
theorem mem_pointHoles (ss : List Segment) (q : ℕ × ℕ) :
    q ∈ pointHoles ss ↔ ∃ s ∈ ss, s.Contains q := by
  simp [pointHoles, List.mem_flatMap, Segment.mem_cells]

/-- Appending physical segment lists takes the union of their actual hole sets. -/
theorem pointHoles_append (ss tt : List Segment) :
    pointHoles (ss ++ tt) = pointHoles ss ∪ pointHoles tt := by
  ext q
  simp [mem_pointHoles, List.mem_append, or_and_right, exists_or]

private theorem holes_card_of_bounds {w h : ℕ} (ss : List Segment)
    (hb : ∀ q ∈ pointHoles ss, q.1 < w ∧ q.2 < h) :
    (holes w h ss).card = (pointHoles ss).card := by
  apply Finset.card_bij (fun (q : Cell w h) _ => (q.1.val, q.2.val))
  · intro q hq
    exact (mem_pointHoles ss _).mpr ((mem_holes ss q).mp hq)
  · intro q _ r _ hqr
    apply Prod.ext
    · exact Fin.ext (congrArg Prod.fst hqr)
    · exact Fin.ext (congrArg Prod.snd hqr)
  · intro q hq
    have hbounds := hb q hq
    refine ⟨(⟨q.1, hbounds.1⟩, ⟨q.2, hbounds.2⟩), ?_, rfl⟩
    exact (mem_holes ss _).mpr ((mem_pointHoles ss q).mp hq)

end SegmentRecipe

namespace PortLayout

/-- Every hole in the actual integer union survives the finite rectangle restriction. -/
theorem encodedSegments_holes_card (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)).card =
      (SegmentRecipe.pointHoles (l.encodedSegments p state)).card := by
  apply SegmentRecipe.holes_card_of_bounds
  intro q hq
  obtain ⟨s, hs, hq⟩ := (SegmentRecipe.mem_pointHoles _ q).mp hq
  have hb := l.encodedSegments_contains_bounds p hl ha state hs hq
  omega

/-- Exact inventory of the emitted fixed/signal union, including all shared physical holes. -/
theorem encodedSegments_holes_card_union (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (state : SignalState) :
    (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state)).card +
      (SegmentRecipe.pointHoles (l.fixedSegments p) ∩
        SegmentRecipe.pointHoles (l.signalSegments p state)).card =
      (SegmentRecipe.pointHoles (l.fixedSegments p)).card +
        (SegmentRecipe.pointHoles (l.signalSegments p state)).card := by
  rw [l.encodedSegments_holes_card p hl ha state, encodedSegments,
    SegmentRecipe.pointHoles_append]
  exact Finset.card_union_add_card_inter _ _

end PortLayout
end PushPuzzle.PushS

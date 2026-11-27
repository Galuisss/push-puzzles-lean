/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramNarrowFixed
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowFixed

/-! The exact fixed-marker row stock also supplies the first row clear's wider retention set. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

/-- The complete actual fixed-point target stock lies on rows retained by the first row clear. -/
theorem acceptanceFixedPointRow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {s : Segment}
    (hs : s ∈ l.fixedSegments p) (hn : s.start = s.finish)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : s.Contains (q.1.val, q.2.val))
    (hframe : q ∉ Boundary.frame) : q.2.val ∈ firstRowKeep l p := by
  have hh := l.acceptanceFixedPointNarrowRow p hl hM hs hn hc hframe
  rcases Finset.mem_union.mp hh with hkeep | hbridge
  · exact Finset.mem_union_left _ hkeep
  · apply Finset.mem_union_right
    have hy := Finset.mem_singleton.mp hbridge
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨0, List.mem_range.mpr p.levels_pos, ?_⟩
    simp only [Nat.zero_add] at *
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    right; right; right
    omega

end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramNarrowFixed
public import PushS.PortReaderBudget
import all Push.AcceptanceProgramNarrowFixed
import all PushS.PortReaderBudget
import all PushS.PortPointBudget
import all PushS.PortSegments
import all PushS.PortEndpointSeparation

/-! Every actual nonpoint fixed segment is either trimmed public corridor or a retained working-row branch. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- A target hole is already read by its public trim, or its row is retained by the first row clear. -/
@[expose] def SecondRowCovered (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2.val ∈ secondRowKeep l p ∨ q ∈ (trimRound l p .upper).region ∨ q ∈ (trimRound l p .lower).region

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

/-- Each actual nonpoint segment is trimmed public corridor or retained working-row stock. -/
theorem acceptanceFixedNonpointNarrowCover (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {s : Segment}
    (hs : s ∈ l.fixedSegments p) (hn : s.start ≠ s.finish)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : s.Contains (q.1.val, q.2.val))
    (hframe : q ∉ Boundary.frame) : SecondRowCovered l p q := by
  rcases l.acceptanceFixedNonpointCover p hl hM hs hn hc hframe with hrow | hu | hd
  · exact Or.inl (Finset.mem_union_left _ hrow)
  · exact Or.inr (Or.inl hu)
  · exact Or.inr (Or.inr hd)

end PushPuzzle.PushS.PortLayout

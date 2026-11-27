/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramNarrowNonpoint
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowFixed
import all PushS.PortPointBudget
import all PushS.PortSegments

/-! Actual near-axis signal holes are retained or consumed by their own main-axis prefix. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The actual main-axis prefix block on one page. -/
def mainRound (l : PortLayout) (p : Scales.Parameters) (side : Side) : Template :=
  .read (if side = .upper then .north else .south)
    ((l.endpoints.filter fun e => e.side == side).map fun e => (p.x e.port, p.Y e.level + 2))

/-- Every endpoint's axis prefix occurs in its own page's emitted main-axis block. -/
theorem endpoint_main_region (l : PortLayout) (p : Scales.Parameters) (e : Endpoint)
    (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port) (hy : pageDepth p e.side q < p.Y e.level + 2) :
    q ∈ (mainRound l p e.side).region := by
  change q ∈ readRegion (if e.side = .upper then .north else .south) _
  apply (mem_readRegion _ _ q).mpr
  refine ⟨(p.x e.port, p.Y e.level + 2), List.mem_map.mpr ⟨e, ?_, rfl⟩, ?_⟩
  · exact List.mem_filter.mpr ⟨he, by simp⟩
  · cases hside : e.side <;>
      simpa only [hside, pageDepth, Direction.lane, prefixRank, reduceCtorEq, ite_true,
        ite_false, Nat.add_sub_cancel] using And.intro hx hy

private theorem branch_row_narrow (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    (if side = .upper then p.Y j + 2 else p.H - (p.Y j + 2)) ∈ secondRowKeep l p := by
  obtain ⟨_, hbranch⟩ := l.workingDepthCoordinates_mem p (j - 1) (by omega)
  have hindex : j - 1 + 1 = j := by omega
  rw [hindex, readDepth_eq p hj hjm] at hbranch
  exact working_row_narrow l p side hbranch

private theorem work_row_narrow (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) :
    (if side = .upper then p.Y j else p.H - p.Y j) ∈ secondRowKeep l p := by
  obtain ⟨hwork, _⟩ := l.workingDepthCoordinates_mem p (j - 1) (by omega)
  have hindex : j - 1 + 1 = j := by omega
  rw [hindex, readDepth_eq p hj hjm] at hwork
  exact working_row_narrow l p side hwork

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem endpoint_signal_narrow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) (e : Endpoint)
    (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (endpointSegments (coordinates p) state e)) :
    q.2.val ∈ secondRowKeep l p ∨ q ∈ (mainRound l p e.side).region := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hb := acceptanceEndpointSignalBand p state e
    ((mem_pointHoles _ _).mpr ((SegmentRecipe.mem_holes _ q).mp hq))
  rw [readDepth_eq p hj hjm] at hb
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  simp only [endpointSegments, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl
  · have hx : q.1.val = p.x e.port := by
      simp only [segment, Segment.Contains, min_self, max_self, coordinates, Coordinates.x,
        Scales.Parameters.x] at hc ⊢
      omega
    by_cases hrow : q.2.val = if e.side = .upper then p.Y e.level + 2 else p.H - (p.Y e.level + 2)
    · exact Or.inl (hrow.symm ▸ branch_row_narrow l p e.side hj hjm)
    · right
      apply endpoint_main_region l p e he hx
      have hH := readDepth_add_lt_H p e.level
      rw [readDepth_eq p hj hjm] at hH
      cases hside : e.side <;>
        simp only [hside, pageDepth, reduceCtorEq, ite_true, ite_false] at hb hrow ⊢ <;> omega
  · left
    have hy := (horizontal_coordinates hc).1
    change q.2.val = onSide (coordinates p) e.side (readDepth p e.level) at hy
    rw [readDepth_eq p hj hjm] at hy
    rw [hy]
    exact work_row_narrow l p e.side hj hjm

set_option maxRecDepth 2048 in
private theorem gate_signal_narrow (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (kind : Shuttle.Kind) (first internal : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (gateSegments (coordinates p) state kind first internal)) :
    q.2.val ∈ secondRowKeep l p := by
  have hb := gateSegments_working_band p state kind first internal
    ((mem_pointHoles _ _).mpr ((SegmentRecipe.mem_holes _ q).mp hq))
  rw [readDepth_eq p le_rfl p.levels_pos] at hb
  have hH := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hH
  rcases (show q.2.val = p.H - p.Y 1 ∨ q.2.val = p.H - p.Y 1 - 1 ∨
    q.2.val = p.H - (p.Y 1 + 2) by omega) with hy | hy | hy
  · rw [hy]
    exact work_row_narrow l p .lower le_rfl p.levels_pos
  · unfold secondRowKeep
    apply Finset.mem_union_right
    exact Finset.mem_singleton.mpr hy
  · rw [hy]
    exact branch_row_narrow l p .lower le_rfl p.levels_pos

/-- All actual signal cells are either retained by the second clear or read on a main axis. -/
theorem acceptanceSignalNarrowCover (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.signalSegments p state)) :
    q.2.val ∈ secondRowKeep l p ∨ q ∈ (mainRound l p .upper).region ∨ q ∈ (mainRound l p .lower).region := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  simp only [signalSegments, rawSignals, List.mem_append, List.mem_flatMap] at hs
  rcases hs with ⟨e, he, hs⟩ | ⟨g, hg, hs⟩
  · have hh := endpoint_signal_narrow l p hl hM state e he ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)
    rcases hh with hh | hh
    · exact Or.inl hh
    · cases hside : e.side
      · exact Or.inr (Or.inl (hside ▸ hh))
      · exact Or.inr (Or.inr (hside ▸ hh))
  · cases hk : g.gate with
    | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
    | some kind =>
      simp only [tripleSignal, hk, Option.elim_some] at hs
      exact Or.inl (gate_signal_narrow l p state kind g.left g.internal ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩))

end PushPuzzle.PushS.PortLayout

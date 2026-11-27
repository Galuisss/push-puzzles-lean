/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointCounts
import all PushS.PortSegments

/-!
# The actual signal holes avoid the central acceptance markers

All raw working levels use the bounded coordinate tables. Their full signal traces stay
more than 32 cells away from the central row, so they avoid every actual fixed hole in
the central marker band.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private def RowBand (p : Scales.Parameters) (s : Segment) : Prop :=
  (s.start.2 + 32 < p.D ∧ s.finish.2 + 32 < p.D) ∨
    (p.D + 32 < s.start.2 ∧ p.D + 32 < s.finish.2)

private theorem side_segment_band (p : Scales.Parameters) (side : Side) {x u y v : ℕ}
    (hy : y + 32 < p.D) (hv : v + 32 < p.D) :
    RowBand p (segment x (onSide (coordinates p) side y) u (onSide (coordinates p) side v)) := by
  have hH : p.H = 2 * p.D := rfl
  unfold RowBand
  cases side with
  | upper =>
    left
    simp [segment, onSide]
    omega
  | lower =>
    right
    simp [segment, onSide, coordinates]
    omega

private theorem endpoint_segment_band (p : Scales.Parameters) (state : SignalState)
    (e : Endpoint) {s : Segment} (hs : s ∈ endpointSegments (coordinates p) state e) :
    RowBand p s := by
  have hy : (coordinates p).depth e.level + 64 < p.D := readDepth_add_lt_D p e.level
  have hbit := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl <;> apply side_segment_band p e.side <;> omega

private theorem triple_segment_band (p : Scales.Parameters) (state : SignalState)
    (g : Placement) {s : Segment} (hs : s ∈ tripleSignal (coordinates p) state g) : RowBand p s := by
  have hy : (coordinates p).depth 1 + 64 < p.D := readDepth_add_lt_D p 1
  dsimp only [tripleSignal, gateSegments] at hs
  cases hg : g.gate with
  | none => simp only [hg, Option.elim_none, List.not_mem_nil] at hs
  | some kind =>
    simp only [hg, Option.elim_some, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl <;> apply side_segment_band p .lower <;> omega

/-- Every actual physical signal hole avoids the central 32-cell band, including raw levels. -/
theorem signalSegments_central_gap (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (l.signalSegments p state)) :
    q.2 + 32 < p.D ∨ p.D + 32 < q.2 := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  have hb : RowBand p s := by
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨e, _, hs⟩ := List.mem_flatMap.mp hs
      exact endpoint_segment_band p state e hs
    · obtain ⟨g, _, hs⟩ := List.mem_flatMap.mp hs
      exact triple_segment_band p state g hs
  simp only [RowBand, Segment.Contains] at hb hq
  omega

/-- Every actual fixed acceptance marker in the central band is disjoint from all signal holes. -/
theorem fixed_central_disjoint_signals (l : PortLayout) (p : Scales.Parameters) (state : SignalState) :
    Disjoint ((pointHoles (l.fixedSegments p)).filter fun q => p.D - 4 ≤ q.2 ∧ q.2 ≤ p.D + 4)
      (pointHoles (l.signalSegments p state)) := by
  apply Finset.disjoint_left.mpr
  intro q hfixed hsignal
  have hband := (Finset.mem_filter.mp hfixed).2
  have hgap := l.signalSegments_central_gap p state hsignal
  omega

end PushPuzzle.PushS.PortLayout

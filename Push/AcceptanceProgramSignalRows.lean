/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramTrim
public import PushS.PortCoreCounts
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! Every real physical signal hole survives the first post-trim row clear. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Every selected working depth occurs literally as a row on either page. -/
theorem working_row_mem (l : PortLayout) (p : Scales.Parameters) (side : Side) {depth : ℕ}
    (hd : depth ∈ l.workingDepthCoordinates p) :
    (if side = .upper then depth else p.H - depth) ∈ workRows l p := by
  apply List.mem_toFinset.mpr
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨depth, hd, ?_⟩
  cases side <;> simp

/-- Every selected working row is retained throughout the initial row clears. -/
theorem working_row_retained (l : PortLayout) (p : Scales.Parameters) (side : Side) {depth : ℕ}
    (hd : depth ∈ l.workingDepthCoordinates p) :
    (if side = .upper then depth else p.H - depth) ∈ keepRows l p :=
  Finset.mem_union_left _ (Finset.mem_union_left _ (working_row_mem l p side hd))

/-- Every actual selected working row survives the first row clear. -/
private theorem working_row_keep (l : PortLayout) (p : Scales.Parameters) (side : Side) {depth : ℕ}
    (hd : depth ∈ l.workingDepthCoordinates p) :
    (if side = .upper then depth else p.H - depth) ∈ firstRowKeep l p :=
  Finset.mem_union_left _ (working_row_retained l p side hd)

/-- The three possible near-axis rows of an allocated level are among the first clear's allowed rows. -/
private theorem level_band_row_keep (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {j depth row : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hlo : p.Y j ≤ depth) (hhi : depth ≤ p.Y j + 2)
    (hrow : row = if side = .upper then depth else p.H - depth) : row ∈ firstRowKeep l p := by
  obtain ⟨hwork, hbranch⟩ := l.workingDepthCoordinates_mem p (j - 1) (by omega)
  have hindex : j - 1 + 1 = j := by omega
  rw [hindex, readDepth_eq p hj hjm] at hwork hbranch
  have hmid : (if side = .upper then p.Y j + 1 else p.H - (p.Y j + 1)) ∈ neighboringRows p := by
    apply List.mem_toFinset.mpr
    apply List.mem_flatMap.mpr
    refine ⟨j - 1, List.mem_range.mpr (by omega), ?_⟩
    simp only [hindex]
    cases side <;> simp
  rw [hrow]
  rcases (show depth = p.Y j ∨ depth = p.Y j + 1 ∨ depth = p.Y j + 2 by omega) with rfl | rfl | rfl
  · exact working_row_keep l p side hwork
  · exact Finset.mem_union_right _ hmid
  · exact working_row_keep l p side hbranch

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe

/-- The complete literal endpoint signal trace stays within its three near-axis page rows. -/
theorem acceptanceEndpointSignalBand (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) :
    if e.side = .upper then readDepth p e.level ≤ q.2 ∧ q.2 ≤ readDepth p e.level + 2
    else p.H - (readDepth p e.level + 2) ≤ q.2 ∧ q.2 ≤ p.H - readDepth p e.level := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hq
  dsimp only [endpointSegments] at hs
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
  have hbit := Bool.toNat_le (if e.side = .upper then state.axes.getD e.port false
    else !(state.axes.getD e.port false))
  rcases hs with rfl | rfl
  all_goals
    cases hside : e.side <;>
      simp only [onSide, hside, reduceCtorEq, ite_true, ite_false, segment, Segment.Contains,
        coordinates, Coordinates.depth, readDepth] at hc hbit ⊢ <;> omega

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

private theorem endpoint_signal_rows_keep (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (state : SignalState) (e : Endpoint)
    (he : e ∈ l.endpoints) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (endpointSegments (coordinates p) state e)) :
    q.2.val ∈ firstRowKeep l p := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hb := acceptanceEndpointSignalBand p state e hq
  rw [readDepth_eq p hj hjm] at hb
  cases hside : e.side
  · simp only [hside, ite_true] at hb
    exact level_band_row_keep l p .upper hj hjm hb.1 hb.2 rfl
  · simp only [hside, reduceCtorEq, ite_false] at hb
    have hy := q.2.isLt
    have hY := readDepth_add_lt_H p e.level
    rw [readDepth_eq p hj hjm] at hY
    apply level_band_row_keep l p .lower hj hjm (depth := p.H - q.2.val)
    · omega
    · omega
    · change q.2.val = p.H - (p.H - q.2.val)
      omega

private theorem gate_signal_rows_keep (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (kind : Shuttle.Kind) (first internal : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : (q.1.val, q.2.val) ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) :
    q.2.val ∈ firstRowKeep l p := by
  have hb := gateSegments_working_band p state kind first internal hq
  rw [readDepth_eq p le_rfl p.levels_pos] at hb
  have hy := q.2.isLt
  have hY := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hY
  apply level_band_row_keep l p .lower le_rfl p.levels_pos (depth := p.H - q.2.val)
  · omega
  · omega
  · change q.2.val = p.H - (p.H - q.2.val)
    omega

/-- Every actual signal-hole cell is retained by the first row clear, for every physical signal state. -/
theorem signal_rows_keep (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (state : SignalState)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.signalSegments p state)) :
    q.2.val ∈ firstRowKeep l p := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  simp only [signalSegments, rawSignals, List.mem_append, List.mem_flatMap] at hs
  rcases hs with ⟨e, he, hs⟩ | ⟨g, hg, hs⟩
  · exact endpoint_signal_rows_keep l p hl hM state e he ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
  · cases hk : g.gate with
    | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
    | some kind =>
      simp only [tripleSignal, hk, Option.elim_some] at hs
      exact gate_signal_rows_keep l p state kind g.left g.internal ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportCoordinatesGeometry
public import PushS.PortWideGeometry
import all Push.AcceptanceSoundnessSupportCoordinatesGuards
import all Push.AcceptanceProgramLayout
import all PushS.PortWideGeometry
import all PushS.PortSegments

/-! The actual rounded wide separators on literal street rows emit genuine guard columns. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

/-- A wide separator on an actual street row is itself a guard witness after conditional rounding. -/
private theorem wideSeparatorHoles_guard_of_streetRow (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p)
    (hrow : q.2.val ∈ streetRowCoordinates p) : q.1.val ∈ guards l p := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hq
  have hp : s.start = s.finish := (List.mem_append.mp hs).elim
    (fun h => (physicalWide_point_row l p .upper h).1)
    (fun h => (physicalWide_point_row l p .lower h).1)
  have hg := (List.mem_append.mp hs).elim
    (fun h => physicalWide_gap l p hl .upper h hc)
    (fun h => physicalWide_gap l p hl .lower h hc)
  have hpoint := hc
  simp only [Segment.Contains, ← hp, min_self, max_self] at hpoint
  have hx : q.1.val = s.start.1 := by omega
  have hy : q.2.val = s.start.2 := by omega
  have hlarge : 14 < 2 * p.b p.levels + 2 := by
    have hY := p.Y_ge p.levels
    have hm := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
      (show 1 ≤ 8 * (p.axes + 1) by omega)
    simp only [Nat.one_mul] at hm
    unfold Scales.Parameters.b
    omega
  apply List.mem_toFinset.mpr
  apply (guard_mem_iff l (coordinates p) (l.fixedSegments p) q.1.val).mpr
  refine ⟨s, List.mem_append_right _ ((List.mem_append.mp hs).elim
    (physicalWide_mem_marked l p .upper) (physicalWide_mem_marked l p .lower)), ?_, hx.symm⟩
  refine ⟨hp, ?_, ?_, ?_⟩
  · simp only [Bool.not_eq_true', Bool.eq_false_iff]
    intro hb
    have hm := List.contains_iff_mem.mp hb
    have hh := hg s.start.1 hm
    rw [hx, Nat.dist_self] at hh
    omega
  · exact List.contains_iff_mem.mpr (hy ▸ hrow)
  · apply List.all_eq_true.mpr
    intro x hx'
    exact decide_eq_true (hlarge.trans (hx ▸ hg x hx'))

/-- With a gate present, the selected depths contain only the literal street rows. -/
private theorem wideSeparatorHoles_streetRow_of_gate (l : PortLayout) (p : Scales.Parameters)
    (hgate : l.gateCenterCoordinates ≠ []) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ l.wideSeparatorHoles p) : q.2.val ∈ streetRowCoordinates p := by
  obtain ⟨side, y, hy, hqy⟩ := l.wideSeparatorHoles_depth p hq
  have hn : (centers l).isEmpty ≠ true := by
    intro he
    cases hec : centers l with
    | nil => exact hgate hec
    | cons a cs => simp only [hec, List.isEmpty_cons, Bool.false_eq_true] at he
  change y ∈ workingRows l (coordinates p) at hy
  obtain ⟨k, hk, hy⟩ := List.mem_flatMap.mp hy
  rw [ite_eq_right hn] at hy
  change q.2.val ∈ [0, p.H] ++ (List.range p.levels).flatMap
    (fun j => [readDepth p (j + 1), readDepth p (j + 1) + 2,
      p.H - readDepth p (j + 1), p.H - (readDepth p (j + 1) + 2)])
  apply List.mem_append_right
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  change y ∈ [readDepth p (k + 1), readDepth p (k + 1) + 2] at hy
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hy ⊢
  cases side <;> simp only [ite_true, reduceCtorEq, ite_false] at hqy <;> omega

/-- All actual wide separators belong to the emitted guard columns when the source contains a gate. -/
theorem wideSeparatorHoles_guard_of_gate (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hgate : l.gateCenterCoordinates ≠ [])
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ l.wideSeparatorHoles p) : q.1.val ∈ guards l p :=
  l.wideSeparatorHoles_guard_of_streetRow p hl hq (l.wideSeparatorHoles_streetRow_of_gate p hgate hq)

end PushPuzzle.PushS.PortLayout

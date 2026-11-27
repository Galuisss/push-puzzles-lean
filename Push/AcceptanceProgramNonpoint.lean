/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramSignalRows
public import PushS.PortReaderBudget
import all PushS.PortReaderBudget
import all PushS.PortPointBudget
import all PushS.PortSegments
import all PushS.PortEndpointSeparation

/-! Every actual nonpoint fixed segment is either trimmed public corridor or a retained working-row branch. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- A target hole is already read by its public trim, or its row is retained by the first row clear. -/
@[expose] def FirstRowCovered (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q.2.val ∈ keepRows l p ∨ q ∈ (trimRound l p .upper).region ∨ q ∈ (trimRound l p .lower).region

end PushPuzzle.Push.AcceptanceProgram

namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem covered_of_trim (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ (trimRound l p side).region) : FirstRowCovered l p q := by
  cases side
  · exact Or.inr (Or.inl hq)
  · exact Or.inr (Or.inr hq)

private theorem endpoint_nonpoint_cover (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (e : Endpoint) (he : e ∈ l.endpoints)
    {s : Segment} (hs : s ∈ endpointFixedSegments l (coordinates p) e) (hn : s.start ≠ s.finish)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : s.Contains (q.1.val, q.2.val)) : FirstRowCovered l p q := by
  by_cases hs2 : s ∈ (endpointFixedSegments l (coordinates p) e).take 2
  · exact covered_of_trim l p e.side (endpoint_corridors_trim l p hl hM e he
      ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs2, hc⟩))
  rw [← List.take_append_drop 3 (endpointFixedSegments l (coordinates p) e), List.mem_append] at hs
  rcases hs with hs | hs
  · dsimp only [endpointFixedSegments] at hs
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl
    · exact False.elim (hs2 (by simp only [endpointFixedSegments, List.cons_append,
        List.nil_append, List.take_succ_cons, List.take_zero, List.mem_cons, true_or]))
    · exact False.elim (hs2 (by simp only [endpointFixedSegments, List.cons_append,
        List.nil_append, List.take_succ_cons, List.take_zero, List.mem_cons, true_or, or_true]))
    · left
      obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
      have hy := (horizontal_coordinates hc).1
      change q.2.val = onSide (coordinates p) e.side (readDepth p e.level + 2) at hy
      rw [readDepth_eq p hj hjm] at hy
      obtain ⟨_, hbranch⟩ := l.workingDepthCoordinates_mem p (e.level - 1) (by omega)
      have hindex : e.level - 1 + 1 = e.level := by omega
      rw [hindex, readDepth_eq p hj hjm] at hbranch
      rw [hy]
      exact working_row_retained l p e.side hbranch
  · exact False.elim (hn (endpoint_tail_points l p e hs))

private theorem gate_nonpoint_cover (l : PortLayout) (p : Scales.Parameters) (middle : ℕ)
    (hi : middle ∈ centers l) {s : Segment} (hs : s ∈ gateFixedSegments (coordinates p) middle)
    (hn : s.start ≠ s.finish) {q : Cell (p.W + 1) (p.H + 1)}
    (hc : s.Contains (q.1.val, q.2.val)) : FirstRowCovered l p q := by
  rw [← List.take_append_drop 4 (gateFixedSegments (coordinates p) middle), List.mem_append] at hs
  rcases hs with hs | hs
  · exact Or.inr (Or.inr (gate_corridors_trim l p middle
      (by simpa only [gateCenterCoordinates] using hi) ((SegmentRecipe.mem_holes _ q).mpr ⟨s, hs, hc⟩)))
  · have hprivate := gate_nonpoint_tail_private p middle hs hn
    dsimp only [gateFixedSegments] at hprivate
    simp only [List.map_cons, List.map_nil, List.cons_append, List.nil_append,
      List.drop_succ_cons, List.drop_zero, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hprivate
    subst s
    left
    have hy := (horizontal_coordinates hc).1
    change q.2.val = onSide (coordinates p) .lower (readDepth p 1 + 2) at hy
    rw [readDepth_eq p le_rfl p.levels_pos] at hy
    obtain ⟨_, hbranch⟩ := l.workingDepthCoordinates_mem p 0 p.levels_pos
    rw [show 0 + 1 = 1 from rfl, readDepth_eq p le_rfl p.levels_pos] at hbranch
    rw [hy]
    exact working_row_retained l p .lower hbranch

/-- Each genuine marked nonpoint segment is covered before the first row clear. -/
theorem acceptanceFixedNonpointCover (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {s : Segment}
    (hs : s ∈ l.fixedSegments p) (hn : s.start ≠ s.finish)
    {q : Cell (p.W + 1) (p.H + 1)} (hc : s.Contains (q.1.val, q.2.val))
    (hframe : q ∉ Boundary.frame) : FirstRowCovered l p q := by
  rcases List.mem_append.mp hs with hs | hs
  · exact False.elim (hframe (frame_contains (coordinates p) q ⟨s, hs, hc⟩))
  have hb := marked_nonpoint_base l p hs hn
  simp only [interiorFixed, List.mem_append, List.mem_flatMap, List.mem_map, or_assoc] at hb
  rcases hb with ⟨e, he, hs⟩ | ⟨middle, hi, hs⟩ | hu | hd | ⟨x, hx, he⟩
  · exact endpoint_nonpoint_cover l p hl hM e he hs hn hc
  · exact gate_nonpoint_cover l p middle hi hs hn hc
  · exact False.elim (hn (wide_points l (coordinates p) .upper hu))
  · exact False.elim (hn (wide_points l (coordinates p) .lower hd))
  · subst s
    exact False.elim (hn rfl)

end PushPuzzle.PushS.PortLayout

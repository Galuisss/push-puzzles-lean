/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramWireRowStock
public import Push.AcceptanceProgramInterlevelStockGeometry
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramNarrowSignals
import all PushS.PortWireRail
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortGateIndexing
import all PushS.PortCoreCrossing
import all PushS.PortSegments

/-! The remaining signal stock on an ordinary work row belongs to its literal WIRE rails. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- The actual allocated horizontal work row on one page. -/
@[expose] def wireWorkRow (p : Scales.Parameters) (side : Side) (j : ℕ) : ℕ :=
  if side = .upper then p.Y j else p.H - p.Y j

private theorem work_band_owner (p : Scales.Parameters) (side other : Side) {i j y : ℕ}
    (hi : 1 ≤ i) (him : i ≤ p.levels) (hj : 1 ≤ j) (hjm : j ≤ p.levels)
    (hy : y = wireWorkRow p side j)
    (hband : if other = .upper then p.Y i ≤ y ∧ y ≤ p.Y i + 2
      else p.H - (p.Y i + 2) ≤ y ∧ y ≤ p.H - p.Y i) :
    other = side ∧ i = j := by
  have hiD := readDepth_add_lt_D p i
  have hjD := readDepth_add_lt_D p j
  rw [readDepth_eq p hi him] at hiD
  rw [readDepth_eq p hj hjm] at hjD
  have hH : p.H = 2 * p.D := rfl
  have hlevels (hnear : p.Y i ≤ p.Y j ∧ p.Y j ≤ p.Y i + 2) : i = j := by
    rcases lt_trichotomy i j with h | h | h
    · have hg := depth_gap p hi h hjm
      rw [readDepth_eq p hi him, readDepth_eq p hj hjm] at hg
      omega
    · exact h
    · have hg := depth_gap p hj h him
      rw [readDepth_eq p hj hjm, readDepth_eq p hi him] at hg
      omega
  cases side <;> cases other <;>
    simp only [wireWorkRow, ite_true, reduceCtorEq, ite_false] at hy hband ⊢
  · exact ⟨trivial, hlevels (by omega)⟩
  · omega
  · omega
  · exact ⟨trivial, hlevels (by omega)⟩

private theorem mainRound_mem_wireWorkPrefix (l : PortLayout) (p : Scales.Parameters)
    (target : List Bool) (side : Side) : mainRound l p side ∈ wireWorkPrefix l p target := by
  cases side <;>
    simp [wireWorkPrefix, schedule, preparation, frameSchedule, mainRound, mainTop, mainBottom]

/-- Every surviving signal on an allocated non-gate work row lies on the open rail of an actual ordinary WIRE. -/
theorem wireWork_signal_rail (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (target : List Bool) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) (hordinary : side = .upper ∨ 2 ≤ j)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ wireWorkReference l p target) (hrow : q.2.val = wireWorkRow p side j)
    (hsig : q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.signalSegments p (l.canonical target))) :
    ∃ g ∈ placements l, g.gate = none ∧ g.side = side ∧ g.level = j ∧ q ∈ wireOpenRail p g := by
  obtain ⟨s, hs, hc⟩ := (SegmentRecipe.mem_holes _ q).mp hsig
  rcases List.mem_append.mp hs with hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    obtain ⟨he0, heM⟩ := l.endpoints_level_bounds p hl hM he
    have hb := acceptanceEndpointSignalBand p (l.canonical target) e
      ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩)
    rw [readDepth_eq p he0 heM] at hb
    obtain ⟨heside, helevel⟩ := work_band_owner p side e.side he0 heM hj hjm hrow hb
    have hmain : q ∉ (mainRound l p e.side).region :=
      emit_stage_excluded (mainRound_mem_wireWorkPrefix l p target e.side) hq
    dsimp only [endpointSegments] at hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    · have hx := (vertical_coordinates hc).1
      apply False.elim
      apply hmain
      apply endpoint_main_region l p e he hx
      have hd := readDepth_add_lt_H p j
      rw [readDepth_eq p hj hjm] at hd
      rw [heside, helevel]
      cases side <;> simp only [pageDepth, wireWorkRow, ite_true, reduceCtorEq, ite_false] at hrow ⊢ <;> omega
    · obtain ⟨g, hg, he⟩ := List.mem_flatMap.mp he
      have hedata : e.side = g.side ∧ e.level = g.level := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl <;> exact ⟨rfl, rfl⟩
      have hgside : g.side = side := hedata.1.symm.trans heside
      have hglevel : g.level = j := hedata.2.symm.trans helevel
      have hw : g.gate = none := by
        cases hk : g.gate with
        | none => rfl
        | some kind =>
          have hs := (placement_gate_shape l hg hk).1
          have hj1 := gate_level_one l hg hk
          rcases hordinary with hu | hj2
          · rw [hgside, hu] at hs
            cases hs
          · omega
      refine ⟨g, hg, hw, hgside, hglevel, ?_⟩
      apply wire_near_subset_rail l p hl (l.canonical target) hg hw
      apply (SegmentRecipe.mem_holes _ q).mpr
      refine ⟨_, ?_, hc⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · apply List.mem_append_left
        simp [wireLeft, endpointSegments]
      · apply List.mem_append_right
        simp [wireRight, endpointSegments, hw]
  · obtain ⟨g, hg, hs⟩ := List.mem_flatMap.mp hs
    cases hk : g.gate with
    | none => simp only [tripleSignal, hk, Option.elim_none, List.not_mem_nil] at hs
    | some kind =>
      have hb := gateSegments_working_band p (l.canonical target) kind g.left g.internal
        ((mem_pointHoles _ _).mpr ⟨s, by simpa only [tripleSignal, hk, Option.elim_some] using hs, hc⟩)
      rw [readDepth_eq p le_rfl p.levels_pos] at hb
      have ho := work_band_owner p side .lower le_rfl p.levels_pos hj hjm hrow
        (show p.H - (p.Y 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - p.Y 1 from ⟨hb.1, hb.2.1⟩)
      rcases hordinary with hu | hj2
      · rw [hu] at ho
        cases ho.1
      · omega

end PushPuzzle.Push.AcceptanceProgram

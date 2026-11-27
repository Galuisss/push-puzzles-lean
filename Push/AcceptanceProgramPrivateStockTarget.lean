/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPrivateStockPrefix
public import PushS.PortGatePrivateWalk
import all PushS.PortGatePrivateWalk
import all PushS.PortGateShuttle
import all PushS.PortCoreCrossing
import all PushS.PortSegments
import all PushS.PortWalkBudget
import all PushS.PortLayoutCoordinates

/-! The four literal private-window holes of every actual canonical gate target. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction SegmentRecipe Push.AcceptanceProgram

private theorem center_placement (l : PortLayout) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) :
    ∃ g ∈ placements l, ∃ kind, g.gate = some kind ∧ g.left + 1 = middle := by
  obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
  obtain ⟨k, hk, he⟩ := List.mem_iff_getElem.mp hg
  refine ⟨⟨.lower, first, first + 2, l.lowerLevel k, l.lowerOffset k, some kind⟩,
    ?_, kind, rfl, hm.symm⟩
  apply List.mem_append_right
  apply List.mem_map.mpr
  refine ⟨(.gate kind first, k), ?_, ?_⟩
  · exact List.mk_mem_zipIdx_iff_getElem?.mpr ((List.getElem?_eq_getElem hk).trans (congrArg some he))
  · simp only [encLowerGroup_elim, encLowerGroup_toSum, Sum.elim_inr]

/-- The actual horizontal gaps always contain the gate's private +4 work-row hole. -/
private theorem private_work_target (l : PortLayout) (p : Scales.Parameters) (state : SignalState)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x middle + 4) (hy : q.2.val = p.H - p.Y 1) :
    q ∈ SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p state) := by
  obtain ⟨g, hg, kind, hk, hmiddle⟩ := center_placement l hi
  have hx' : q.1.val = (coordinates p).x (g.left + 1) + 4 := by
    change q.1.val = p.x (g.left + 1) + 4
    rw [hmiddle]
    exact hx
  have hy' : q.2.val = onSide (coordinates p) .lower ((coordinates p).depth 1) := by
    change q.2.val = p.H - readDepth p 1
    rw [readDepth_eq p le_rfl p.levels_pos]
    exact hy
  have hc : (q.1.val, q.2.val) ∈ pointHoles (gateSegments (coordinates p) state kind g.left g.internal) := by
    have hl := Bool.toNat_le (state.internal.getD g.internal false)
    have hr := Bool.toNat_le (state.internal.getD (g.internal + 2) false)
    have hκ : 2 ≤ kappaNat kind ∧ kappaNat kind ≤ 4 := by cases kind <;> decide +kernel
    cases hs : state.internal.getD (g.internal + 1) false
    · apply (mem_pointHoles _ _).mpr
      refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
      simp only [hs, Bool.false_eq_true, ite_false]
      apply (horizontal_contains _ _ _ _).mpr
      exact ⟨hy', by omega, by omega⟩
    · apply (mem_pointHoles _ _).mpr
      refine ⟨_, List.mem_cons_self .., ?_⟩
      simp only [hs, ite_true]
      apply (horizontal_contains _ _ _ _).mpr
      exact ⟨hy', by omega, by omega⟩
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp (core_signal_mem l p state hg hk hc)
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs, hc⟩

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Each of the four owned private depths names a literal canonical target hole. -/
theorem private_four_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ privateColumns l p) {depth : ℕ}
    (hd : depth ∈ ({p.Y 1 / 2, p.Y 1, p.Y 1 + 1, p.Y 1 + 2} : Finset ℕ))
    (hy : q.2.val = p.H - depth) : q ∈ targetHoles l p target := by
  obtain ⟨i, hi, hx'⟩ := privateColumn_gate l p hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl | rfl
  · exact half_target l p target hy (Finset.mem_union_right _ hx)
  · exact l.private_work_target p (l.canonical target) hi hx' hy
  · apply l.gatePrivateWalk_subset_encoded p (l.canonical target) hi
    apply (mem_gatePrivateWalk p i).mpr
    right
    left
    exact ⟨hx', by simpa only [readDepth_eq p le_rfl p.levels_pos] using hy⟩
  · apply l.gatePrivateWalk_subset_encoded p (l.canonical target) hi
    apply (mem_gatePrivateWalk p i).mpr
    right
    right
    refine ⟨?_, ?_, ?_⟩
    · simpa only [readDepth_eq p le_rfl p.levels_pos] using hy
    · omega
    · exact hx'.le

end PushPuzzle.Push.AcceptanceProgram

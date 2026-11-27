/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramMainStockGeometry
public import PushS.PortEndpointReadouts
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramPrefix
import all PushS.PortOrdinaryAxis

/-! A genuine gate word at the upper threshold has exactly the first two holes in the main-read front. -/

public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

private theorem gate_upper_front_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} {upper : Endpoint} (hu : upper ∈ l.endpoints)
    (hs : upper.side = .upper) (hp : upper.port = g.left + 1)
    {t : State (p.W + 1) (p.H + 1)} {a : GateAxisPlacement}
    (word : GateAxisReadout p g upper t a) (hshift : a.upperShift = 0) (hthreshold : a.parameter ≤ 1) :
    ((holes t ∩ ordinaryAxis p upper.port).filter fun q =>
      q ∈ (Scan.lineCells .north (p.x upper.port)).take (readDepth p upper.level + 2)) =
        mainSourceFront l p target upper := by
  classical
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hu
  have hY := readDepth_ge p hj hjm
  have hD := readDepth_add_lt_D p upper.level
  have hH : p.H = 2 * p.D := rfl
  have hread := readDepth_eq p hj hjm
  ext q
  rw [mem_mainSourceFront l p hl hM haxes target upper hu q]
  constructor
  · intro hq
    obtain ⟨hq, hfront⟩ := Finset.mem_filter.mp hq
    obtain ⟨hhole, haxis⟩ := Finset.mem_inter.mp hq
    obtain ⟨_, hx, hy0, hyH⟩ := Finset.mem_filter.mp haxis
    have hfront := (mem_line_prefix .north _ _ q).mp hfront
    change q.1.val = p.x upper.port ∧ q.2.val < readDepth p upper.level + 2 at hfront
    have hword := (word.upper_holes q (hx.trans (congrArg p.x hp)) ⟨hy0, by omega⟩).mp hhole
    rw [hshift] at hword
    refine ⟨hx, ?_⟩
    simp only [pageDepth, hs, ite_true]
    omega
  · rintro ⟨hx, hy⟩
    simp only [pageDepth, hs, ite_true] at hy
    have hy0 : 0 < q.2.val ∧ q.2.val < p.D := by omega
    have hhole : q ∈ holes t := (word.upper_holes q (hx.trans (congrArg p.x hp)) hy0).mpr (by
      rw [hshift]
      right
      omega)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_inter.mpr ⟨hhole, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx, hy0.1, by omega⟩⟩, ?_⟩
    apply (mem_line_prefix .north _ _ q).mpr
    change q.1.val = p.x upper.port ∧ q.2.val < readDepth p upper.level + 2
    exact ⟨hx, by omega⟩

end PushPuzzle.Push.AcceptanceSoundness

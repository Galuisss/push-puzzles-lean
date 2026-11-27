/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGateCoreMotion
import all PushS.PortLayoutCoordinates

/-! Every actual gate private region lies strictly in the lower half of the board. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Actual G lies strictly below the board's middle line. -/
theorem gateLeftGap_below_midline (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (a : Shuttle.Placement)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateLeftGap p g kind a) : p.D < q.2.val := by
  have hy := (Finset.mem_filter.mp hq).2.1
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  omega

/-- Actual J lies strictly below the board's middle line. -/
theorem gateRightGap_below_midline (p : Scales.Parameters) (g : Placement) (a : Shuttle.Placement)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateRightGap p g a) : p.D < q.2.val := by
  have hy := (Finset.mem_filter.mp hq).2.1
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  omega

/-- Every closed core near interval with an actual parameter in 0..3 lies below the middle line. -/
theorem gateAxisNear_below_midline (p : Scales.Parameters) (g : Placement) {parameter : ℕ} (hp : parameter ≤ 3)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateAxisNear p g parameter) : p.D < q.2.val := by
  have hy := (Finset.mem_filter.mp hq).2
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  omega

/-- All five actual private branch cells lie below the middle line. -/
theorem gatePrivateCells_below_midline (p : Scales.Parameters) (middle : ℕ)
    {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gatePrivateCells p middle) : p.D < q.2.val := by
  have hy := (Finset.mem_filter.mp hq).2
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  rcases hy with hy | hy <;> omega

/-- The complete low-core private region is strictly below the middle line. -/
theorem gateLowCorePrivate_below_midline (p : Scales.Parameters) (g : Placement) (kind : Shuttle.Kind) (state : GateCorePlacement)
    (hp : state.axis.parameter ≤ 3) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateLowCorePrivate p g kind state) :
    p.D < q.2.val := by
  rcases Finset.mem_union.mp hq with hq | hq
  · rcases Finset.mem_union.mp hq with hq | hq
    · exact gateLeftGap_below_midline p g kind _ hq
    · exact gateAxisNear_below_midline p g hp hq
  · by_cases hfour : gateFourInG p g kind state
    · rw [ite_eq_left hfour] at hq
      exact gatePrivateCells_below_midline p _ hq
    · rw [ite_eq_right hfour] at hq
      exact False.elim (Finset.notMem_empty _ hq)

/-- The complete AND left-fault private region is strictly below the middle line. -/
theorem gateAndLeftPrivate_below_midline (p : Scales.Parameters) (g : Placement) (state : GateCorePlacement)
    (hp : state.axis.parameter ≤ 3) {q : Cell (p.W + 1) (p.H + 1)} (hq : q ∈ gateAndLeftPrivate p g state) :
    p.D < q.2.val := by
  rcases Finset.mem_union.mp hq with hq | hq
  · exact gateLeftGap_below_midline p g .andGate _ hq
  · by_cases hfour : gateFourInG p g .andGate state
    · rw [ite_eq_left hfour] at hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact gatePrivateCells_below_midline p _ hq
      · exact gateAxisNear_below_midline p g hp hq
    · rw [ite_eq_right hfour] at hq
      exact False.elim (Finset.notMem_empty _ hq)

end PushPuzzle.PushS.PortLayout

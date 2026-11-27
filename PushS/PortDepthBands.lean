/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortOrdinaryBlockers
import all PushS.PortWireGeometry
import all PushS.PortSegments
import all PushS.PortStreetSeparation

/-! Selected work rows lie in an endpoint's shallow, branch, or protected deep band. -/

public section
namespace PushPuzzle.PushS.PortLayout


/-- A selected depth is shallow, the endpoint's branch row, or beyond its interlevel marker. -/
theorem workingDepthCoordinates_bands (l : PortLayout) (p : Scales.Parameters)
    {j v : ℕ} (hj : 1 ≤ j) (hjM : j ≤ p.levels) (hv : v ∈ l.workingDepthCoordinates p) :
    v ≤ readDepth p j ∨ v = readDepth p j + 2 ∨
      (j < p.levels ∧ (readDepth p j + readDepth p (j + 1)) / 2 ≤ v) := by
  obtain ⟨k, hk, hv⟩ := List.mem_flatMap.mp hv
  have hk : k < p.levels := List.mem_range.mp hk
  change v ∈ (if (centers l).isEmpty then
    [readDepth p (k + 1) - 2, readDepth p (k + 1), readDepth p (k + 1) + 2]
    else [readDepth p (k + 1), readDepth p (k + 1) + 2]) at hv
  have hspan : readDepth p (k + 1) - 2 ≤ v ∧ v ≤ readDepth p (k + 1) + 2 := by
    split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega
  by_cases hkj : k + 1 < j
  · have hg := depth_gap p (show 1 ≤ k + 1 by omega) hkj hjM
    exact Or.inl (by omega)
  · by_cases heq : k + 1 = j
    · rw [heq] at hv
      split at hv <;> simp only [List.mem_cons, List.not_mem_nil, or_false] at hv <;> omega
    · have hnext := next_depth_le p hj (show j < k + 1 by omega) (show k + 1 ≤ p.levels by omega)
      have hgap := readDepth_interlevel_margin p hj (show j < p.levels by omega)
      exact Or.inr (Or.inr ⟨by omega, by omega⟩)

end PushPuzzle.PushS.PortLayout

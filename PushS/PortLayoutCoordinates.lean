/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortLayout

/-!
# Uniform margins for the actual bounded coordinate reads

Every raw level reads either an allocated geometric coordinate or zero. Thus the same
outer-scale margin bounds every call made by the segment emitter, including raw levels
above the allocated table. The horizontal margin includes the emitter's local offsets.

## Main results

* `PortLayout.readDepth_readLength_margin`: every raw lookup leaves 64 cells before `D`.
* `PortLayout.readLength_add_lt_x`: long branches and local offsets stay right of zero.
* `PortLayout.x_add_readLength_lt_W`: bounded port axes leave the same margin on the right.
-/

public section

namespace PushPuzzle.PushS.PortLayout


private theorem Y_le (p : Scales.Parameters) {j k : ℕ} (hjk : j ≤ k) : p.Y j ≤ p.Y k := by
  unfold Scales.Parameters.Y
  exact Nat.mul_le_mul_left p.A (Nat.pow_le_pow_right
    (by unfold Scales.Parameters.S; omega) (by omega))

private theorem L_le (p : Scales.Parameters) {j k : ℕ} (hjk : j ≤ k) : p.L j ≤ p.L k := by
  by_cases hj : j = 0
  · simp [Scales.Parameters.L, hj]
  · have hk : k ≠ 0 := by omega
    simp only [Scales.Parameters.L, hj, hk, ite_false]
    exact Nat.mul_le_mul_left p.A (Nat.pow_le_pow_right
      (by unfold Scales.Parameters.S; omega) (by omega))

/-- Every raw working-row lookup is at most the last allocated working row. -/
theorem readDepth_le_last (p : Scales.Parameters) (j : ℕ) : readDepth p j ≤ p.Y p.levels := by
  by_cases hj : j = 0
  · simp [readDepth, depthTable, hj]
  · by_cases hm : j ≤ p.levels
    · rw [readDepth_eq p (by omega) hm]
      exact Y_le p hm
    · rw [readDepth_eq_zero p (by omega)]
      exact Nat.zero_le _

/-- Every raw branch-length lookup is at most the last allocated branch length. -/
theorem readLength_le_last (p : Scales.Parameters) (j : ℕ) :
    readLength p j ≤ p.L p.levels := by
  by_cases hj : j = 0
  · simp [readLength, lengthTable, hj]
  · by_cases hm : j ≤ p.levels
    · rw [readLength_eq p (by omega) hm]
      exact L_le p hm
    · rw [readLength_eq_zero p (by omega)]
      exact Nat.zero_le _

/-- The actual tables retain the outer-scale margin on every raw lookup. -/
theorem readDepth_readLength_margin (p : Scales.Parameters) (j k : ℕ) :
    readDepth p j + readLength p k + 64 < p.D := by
  have hy := readDepth_le_last p j
  have hl := readLength_le_last p k
  have ho := p.outer_distance
  have hb : p.Y p.levels + p.L p.levels + 10 ≤ p.b p.levels := by
    have hm := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
      (show 1 ≤ 8 * (p.axes + 1) by omega)
    unfold Scales.Parameters.b
    simp only [Nat.one_mul] at hm
    omega
  omega

/-- Allocated working rows have the literal lower depth bound used by the near-axis holes. -/
theorem readDepth_ge (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hm : j ≤ p.levels) :
    16384 ≤ readDepth p j := by
  rw [readDepth_eq p hj hm]
  exact p.Y_ge j

/-- Allocated branch lengths retain the same positive depth floor. -/
theorem readLength_ge (p : Scales.Parameters) {j : ℕ} (hj : 1 ≤ j) (hm : j ≤ p.levels) :
    16384 ≤ readLength p j := by
  rw [readLength_eq p hj hm, p.L_eq j hj]
  have hy := p.Y_ge j
  have hs : 1 ≤ p.S := by unfold Scales.Parameters.S; omega
  have hp := Nat.mul_le_mul_left (p.Y j) hs
  simp only [Nat.mul_one] at hp
  omega

/-- The literal interlevel spacing holds for the actual successive table reads. -/
theorem readDepth_interlevel_margin (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hm : j < p.levels) :
    2 * p.b j + 6 < (readDepth p (j + 1) - readDepth p j) / 2 - 2 := by
  rw [readDepth_eq p (by omega) (by omega), readDepth_eq p hj (by omega)]
  exact p.interlevel_margin j hj

/-- Every port axis lies beyond all allocated branch lengths and local offsets. -/
theorem readLength_add_lt_x (p : Scales.Parameters) (i j : ℕ) :
    readLength p j + 64 < p.x i := by
  have hm := readDepth_readLength_margin p 0 j
  have hx : p.D ≤ p.x i := by
    unfold Scales.Parameters.x
    simpa using Nat.mul_le_mul_right p.D (show 1 ≤ i + 1 by omega)
  omega

/-- Every declared port axis leaves room for a long branch and the local offsets. -/
theorem x_add_readLength_lt_W (p : Scales.Parameters) {i : ℕ} (hi : i < p.axes) (j : ℕ) :
    p.x i + readLength p j + 64 < p.W := by
  have hm := readDepth_readLength_margin p 0 j
  have hx : p.x i ≤ p.axes * p.D := by
    unfold Scales.Parameters.x
    exact Nat.mul_le_mul_right p.D (by omega)
  rw [Scales.Parameters.W, Nat.add_mul, Nat.one_mul]
  omega

/-- All working depths and local row offsets remain strictly above the central row. -/
theorem readDepth_add_lt_D (p : Scales.Parameters) (j : ℕ) : readDepth p j + 64 < p.D := by
  have hm := readDepth_readLength_margin p j 0
  omega

/-- Reflecting an allocated row and its local offsets stays within the board height. -/
theorem readDepth_add_lt_H (p : Scales.Parameters) (j : ℕ) : readDepth p j + 64 < p.H := by
  have hm := readDepth_add_lt_D p j
  unfold Scales.Parameters.H
  omega

/-- The actual central markers at distance four lie inside the two-page rectangle. -/
theorem central_marker_bounds (p : Scales.Parameters) : 4 < p.D ∧ p.D + 4 < p.H := by
  have hm := readDepth_add_lt_D p 0
  unfold Scales.Parameters.H
  omega

end PushPuzzle.PushS.PortLayout

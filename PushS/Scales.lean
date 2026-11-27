/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-! Closed geometric scales and their arithmetic separation budgets. -/

@[expose] public section
namespace PushPuzzle.PushS.Scales


/-- Number of main axes and allocated working levels. -/
structure Parameters where
  axes : ℕ
  levels : ℕ
  axes_pos : 1 ≤ axes
  levels_pos : 1 ≤ levels

namespace Parameters

def Q (p : Parameters) : ℕ := 512 * (p.axes + 1) * (p.levels + 1)
def S (p : Parameters) : ℕ := 64 * (p.axes + 1)
def A (p : Parameters) : ℕ := 8 * p.Q
def Y (p : Parameters) (j : ℕ) : ℕ := p.A * p.S ^ (2 * j - 2)
def L (p : Parameters) (j : ℕ) : ℕ :=
  if j = 0 then 0 else p.A * p.S ^ (2 * j - 1)
def D (p : Parameters) : ℕ := p.A * p.S ^ (2 * p.levels)
def W (p : Parameters) : ℕ := (p.axes + 1) * p.D
def H (p : Parameters) : ℕ := 2 * p.D
def x (p : Parameters) (i : ℕ) : ℕ := (i + 1) * p.D

/-- Arithmetic upper budget used between levels. -/
def b (p : Parameters) (j : ℕ) : ℕ :=
  p.Q + 8 * (p.axes + 1) * (p.Y j + p.L j + 10)

/-- Arithmetic upper budget used at one reader layer. -/
def K (p : Parameters) (j : ℕ) : ℕ :=
  p.Q + 4 * p.axes * (p.Y j + 2) + 2 * p.axes * p.L (j - 1)

variable (p : Parameters)

private theorem Q_ge : 2048 ≤ p.Q := by
  unfold Q
  have hn := p.axes_pos
  have hm := p.levels_pos
  nlinarith

private theorem S_ge : 128 ≤ p.S := by
  unfold S
  have hn := p.axes_pos
  omega

theorem Y_ge_A (j : ℕ) : p.A ≤ p.Y j := by
  have hs : 0 < p.S := by have := p.S_ge; omega
  have hp : 1 ≤ p.S ^ (2 * j - 2) := pow_pos hs _
  simpa only [Y, Nat.mul_one] using Nat.mul_le_mul_left p.A hp

theorem Y_ge (j : ℕ) : 16384 ≤ p.Y j := by
  have hQ := p.Q_ge
  have hY := p.Y_ge_A j
  unfold A at hY
  omega

theorem L_eq (j : ℕ) (hj : 1 ≤ j) : p.L j = p.Y j * p.S := by
  rw [L, ite_eq_right (by omega), Y]
  rw [show 2 * j - 1 = (2 * j - 2) + 1 by omega, pow_succ]
  ring

theorem Y_succ (j : ℕ) (hj : 1 ≤ j) : p.Y (j + 1) = p.Y j * p.S ^ 2 := by
  unfold Y
  rw [show 2 * (j + 1) - 2 = (2 * j - 2) + 2 by omega, pow_add]
  ring

private theorem D_eq_last : p.D = p.Y p.levels * p.S ^ 2 := by
  unfold D Y
  conv_lhs =>
    rw [show 2 * p.levels = (2 * p.levels - 2) + 2 by have := p.levels_pos; omega,
      pow_add]
  ring

private theorem L_previous_le (j : ℕ) (hj : 1 ≤ j) : p.L (j - 1) ≤ p.Y j := by
  by_cases he : j = 1
  · subst j
    simp [L]
  · have hprod : p.L (j - 1) * p.S = p.Y j := by
      rw [L, ite_eq_right (by omega), Y]
      rw [show 2 * j - 2 = (2 * (j - 1) - 1) + 1 by omega, pow_succ]
      ring
    have hs : 1 ≤ p.S := by have := p.S_ge; omega
    have h := Nat.mul_le_mul_left (p.L (j - 1)) hs
    simpa only [Nat.mul_one, hprod] using h

private theorem Q_le_Y (j : ℕ) : p.Q ≤ p.Y j := by
  have h := p.Y_ge_A j
  unfold A at h
  omega

/-- Reader separation after accounting for shallower lines and local offsets. -/
theorem reader_distance (j : ℕ) (hj : 1 ≤ j) :
    p.K j < p.L j / 2 - p.L (j - 1) - 12 := by
  have hQ := p.Q_le_Y j
  have hY := p.Y_ge j
  have hprev := p.L_previous_le j hj
  have hmul := Nat.mul_le_mul_left (2 * p.axes) hprev
  have h8 := Nat.mul_le_mul_left p.axes (show 8 ≤ p.Y j by omega)
  have hstrong : 2 * (p.K j + p.L (j - 1) + 13) ≤ p.L j := by
    rw [K, p.L_eq j hj, S]
    nlinarith
  omega

private theorem strong_growth (j : ℕ) (hj : 1 ≤ j) :
    4 * (p.b j + p.L j + p.Y j + 20) < p.Y j * p.S ^ 2 := by
  have hQ := p.Q_le_Y j
  have hY := p.Y_ge j
  have hN : 1 ≤ p.axes + 1 := by omega
  have hNN : p.axes + 1 ≤ (p.axes + 1) ^ 2 := by nlinarith
  have hNY := Nat.mul_le_mul_right (p.Y j) hNN
  have hYY : p.Y j ≤ (p.axes + 1) ^ 2 * p.Y j := by
    have h := Nat.mul_le_mul_right (p.Y j) (show 1 ≤ (p.axes + 1) ^ 2 by nlinarith)
    simpa only [Nat.one_mul] using h
  have h10 := Nat.mul_le_mul_left (p.axes + 1) (show 10 ≤ p.Y j by omega)
  have hpos : 0 < (p.axes + 1) ^ 2 * p.Y j := by positivity
  rw [b, p.L_eq j hj, S]
  nlinarith

/-- The midpoint gap retains the full doubled-budget margin. -/
theorem interlevel_margin (j : ℕ) (hj : 1 ≤ j) :
    2 * p.b j + 6 < (p.Y (j + 1) - p.Y j) / 2 - 2 := by
  have hg := p.strong_growth j hj
  rw [p.Y_succ j hj]
  omega

/-- The outer scale separates both pages and all widest local lines. -/
theorem outer_distance : 4 * (p.b p.levels + p.L p.levels + 10) < p.D := by
  have hg := p.strong_growth p.levels p.levels_pos
  rw [p.D_eq_last]
  omega

/-- The outer scale as a single power in the number of axes. -/
private theorem D_closed :
    p.D = (4096 * (p.levels + 1) * 64 ^ (2 * p.levels)) *
      (p.axes + 1) ^ (2 * p.levels + 1) := by
  unfold D A Q S
  rw [mul_pow, pow_succ]
  ring

/-- Inclusive rectangle area, bounded by one explicit monomial at each fixed level count. -/
theorem area_le :
    (p.W + 1) * (p.H + 1) ≤
      6 * (4096 * (p.levels + 1) * 64 ^ (2 * p.levels)) ^ 2 *
        (p.axes + 1) ^ (4 * p.levels + 3) := by
  have hD : 1 ≤ p.D := by
    have h := p.outer_distance
    omega
  have hW : p.W + 1 ≤ 2 * (p.axes + 1) * p.D := by
    unfold W
    have h := Nat.mul_le_mul_right p.D (show 1 ≤ p.axes + 1 by omega)
    nlinarith
  have hH : p.H + 1 ≤ 3 * p.D := by unfold H; omega
  calc
    (p.W + 1) * (p.H + 1) ≤ (2 * (p.axes + 1) * p.D) * (3 * p.D) :=
      Nat.mul_le_mul hW hH
    _ = 6 * (4096 * (p.levels + 1) * 64 ^ (2 * p.levels)) ^ 2 *
          ((p.axes + 1) ^ ((2 * p.levels + 1) * 2) * (p.axes + 1)) := by
      simp only [p.D_closed, mul_pow, ← pow_mul]
      ring
    _ = 6 * (4096 * (p.levels + 1) * 64 ^ (2 * p.levels)) ^ 2 *
          (p.axes + 1) ^ (4 * p.levels + 3) := by
      rw [← pow_succ, show (2 * p.levels + 1) * 2 + 1 = 4 * p.levels + 3 by omega]

end Parameters
end PushPuzzle.PushS.Scales

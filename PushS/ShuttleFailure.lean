/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Shuttle

/-! The five geometric fault classes cover every failed AND/OR external interface. -/

@[expose] public section
namespace PushPuzzle.PushS.Shuttle


/-- Two ordinary-axis parameters and the middle axis's near-hole count. -/
structure External where
  left : ℕ
  middle : ℕ
  right : ℕ

/-- Input thresholds for the complete three-port group. -/
def External.Legal (k : Kind) (e : External) : Prop :=
  match k with
  | .orGate => e.left ≤ 1 ∨ 2 ≤ e.middle ∨ e.right ≤ 1
  | .andGate => e.right ≤ 1 ∨ (e.left ≤ 1 ∧ 2 ≤ e.middle)

/-- W at either outer endpoint, R, O, K_C, and K_B in the double-box geometry. -/
inductive Fault (k : Kind) (a : Placement) (e : External) : Prop
  | leftWire (axis : 2 ≤ e.left) (horizontal : a.left ≤ 1)
  | rightWire (axis : 2 ≤ e.right) (horizontal : a.right ≤ 1)
  | relay (short : 6 ≤ a.short) (right : 2 ≤ a.right)
  | orCore (kind : k = .orGate) (left : 2 ≤ a.left) (short : a.short ≤ 5)
      (middle : e.middle ≤ 1)
  | andCenter (kind : k = .andGate) (short : a.short ≤ 5) (middle : e.middle ≤ 1)
  | andLeft (kind : k = .andGate) (short : a.short ≤ 5) (left : 2 ≤ a.left)

/-- Every failed external interface falls into a local fault class. -/
theorem fault_of_illegal (k : Kind) (a : Placement) (e : External)
    (hbad : ¬ e.Legal k) : Fault k a e := by
  cases k with
  | orGate =>
    have hl : 2 ≤ e.left := by simp only [External.Legal] at hbad; omega
    have hm : e.middle ≤ 1 := by simp only [External.Legal] at hbad; omega
    have hr : 2 ≤ e.right := by simp only [External.Legal] at hbad; omega
    by_cases hal : a.left ≤ 1
    · exact .leftWire hl hal
    by_cases har : a.right ≤ 1
    · exact .rightWire hr har
    by_cases hap : 6 ≤ a.short
    · exact .relay hap (by omega)
    · exact .orCore rfl (by omega) (by omega) hm
  | andGate =>
    have hr : 2 ≤ e.right := by simp only [External.Legal] at hbad; omega
    have hlight : 2 ≤ e.left ∨ e.middle ≤ 1 := by
      simp only [External.Legal] at hbad
      omega
    by_cases har : a.right ≤ 1
    · exact .rightWire hr har
    by_cases hap : 6 ≤ a.short
    · exact .relay hap (by omega)
    rcases hlight with hl | hm
    · by_cases hal : a.left ≤ 1
      · exact .leftWire hl hal
      · exact .andLeft rfl (by omega) (by omega)
    · exact .andCenter rfl (by omega) hm

end PushPuzzle.PushS.Shuttle

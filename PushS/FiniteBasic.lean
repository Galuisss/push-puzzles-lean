/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Basic

/-! Finite pushing and exact storage on a rectangle with no fixed walls. -/

@[expose] public section
namespace PushPuzzle.PushS

/-- Exact storage with at most `k` boxes pushed in one move. -/
def Instance.SolvableFinite (I : Instance) (k : ℕ) : Prop :=
  I.toInstance.Solvable (some k)

/-- The wall-free storage language at a fixed finite push cap. -/
def solvableFinite (k : ℕ) : Set Instance := {I | I.SolvableFinite k}

/-- Increasing the finite push cap preserves storage solutions. -/
theorem Instance.SolvableFinite.mono {I : Instance} {k l : ℕ} (hkl : k ≤ l)
    (hI : I.SolvableFinite k) : I.SolvableFinite l := by
  obtain ⟨t, hr, ht⟩ := hI
  exact ⟨t, hr.mono (cap' := some l) (fun _ hn => Nat.le_trans hn hkl), ht⟩

end PushPuzzle.PushS

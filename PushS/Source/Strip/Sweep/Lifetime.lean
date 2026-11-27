/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Scan

/-!
# Actual unit-arc lifetimes in the strip scan

A horizontal unit arc persists for one scan column, and a vertical unit arc for one scan step.
Every actual local incidence is therefore within one fixed scan radix of its creation position.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.Arc.birth`: the actual scan position creating a unit arc.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.Arc.level_span_le`: a unit arc's complete scan lifetime is at most one radix.
* `PushPuzzle.NCL.Strip.Sweep.local_birth_bounds`: the same bound for every actual local incoming/outgoing arc.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

namespace Arc

open Cslib.Complexity Cslib.Complexity.NCL

/-- The actual integer scan position at which the unit arc is created. -/
@[expose] def birth (a : Arc R) : ℤ := level K (a.lower R)

/-- A unit arc lasts one vertical scan step or one complete column scan, at most one radix. -/
theorem level_span_le (a : Arc R) :
    level K (a.upper R) ≤ a.birth R + (height K + 1 : ℕ) := by
  rcases a.shape R with h | h
  · simp only [birth, level, h, mul_add, mul_one]
    omega
  · simp only [birth, level, h]
    omega

/-- Both endpoints of an actual unit arc occur within its actual bounded scan lifetime. -/
private theorem birth_bounds (a : Arc R) {p : Point} (h : a.lower R = p ∨ a.upper R = p) :
    a.birth R ≤ level K p ∧ level K p ≤ a.birth R + (height K + 1 : ℕ) := by
  rcases h with h | h
  · rw [← h]
    exact ⟨le_rfl, by dsimp only [birth]; omega⟩
  · rw [← h]
    exact ⟨(a.level_lt R).le, a.level_span_le R⟩

end Arc

/-- Every actual local incoming or outgoing arc is within one radix of its birth scan position.
-/
theorem local_birth_bounds (es : List E) (t : ℤ) {a : Arc R}
    (ha : a ∈ (slice R es (scanPoint K t)).incoming ++
      (slice R es (scanPoint K t)).outgoing) :
    a.birth R ≤ t ∧ t ≤ a.birth R + (height K + 1 : ℕ) := by
  have hp : a.lower R = scanPoint K t ∨ a.upper R = scanPoint K t := by
    rcases List.mem_append.mp ha with hi | ho
    · exact Or.inr ((mem_slice_incoming R es _ a).mp hi).2
    · exact Or.inl ((mem_slice_outgoing R es _ a).mp ho).2
  simpa only [level_scanPoint] using a.birth_bounds R hp

end PushPuzzle.NCL.Strip.Sweep

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Window
public import CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.Orthogonal

/-!
# Complete continuous support windows of the actual simple routes

The existing normalization turns each complete grid path into a simple unit route. Every listed
point remains on the original path, and every real segment between consecutive points stays
inside the same rectangle. Thus the entire continuous support has the same strip window.

## Main results

* `PushPuzzle.NCL.GridDrawing.Closed.unitRoute_window`: complete actual simple polyline support in a fixed window.
-/

public section

namespace PushPuzzle.NCL.GridDrawing

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib Cslib.Orthogonal

variable {V E : Type*} {G : ConstraintGraph V E} (P : Closed G)

/-- Passing to the actual simple unit route retains the entire continuous strip support window.
-/
theorem Closed.unitRoute_window {width span : ℕ}
    (h : ∀ e, ∃ start : ℕ, ∀ p, (P.path e).Contains p →
      p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span) :
    ∀ e, ∃ start : ℕ, ∀ q : ℝ × ℝ, q ∈ support (P.path e).unitRoute →
      0 ≤ q.1 ∧ q.1 ≤ width ∧ (start : ℝ) ≤ q.2 ∧ q.2 ≤ (start : ℝ) + span := by
  intro e
  obtain ⟨start, hs⟩ := h e
  refine ⟨start, fun q hq => ?_⟩
  have hpoints (r : Cslib.Orthogonal.Point) (hr : r ∈ (P.path e).unitRoute) :
      (0 : ℤ) ≤ r.1 ∧ r.1 ≤ (width : ℤ) ∧ (start : ℤ) ≤ r.2 ∧
        r.2 ≤ ((start + span : ℕ) : ℤ) := by
    obtain ⟨p, hp, hmem⟩ := (P.path e).unitRoute_trace r hr
    have hb := hs p hmem
    rw [← hp]
    dsimp only [integerPoint]
    exact_mod_cast (show 0 ≤ p.1 ∧ p.1 ≤ width ∧ start ≤ p.2 ∧ p.2 ≤ start + span from
      ⟨Nat.zero_le _, hb⟩)
  have hb := support_bounds_of_points hpoints hq
  simpa only [Int.cast_zero, Int.cast_add, Int.cast_natCast, Nat.cast_add] using hb

end PushPuzzle.NCL.GridDrawing

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Init
public import CslibFrontier.Foundations.Geometry.Orthogonal

/-!
# Segment membership at strict transverse crossings

## Main results

* `PushPuzzle.Orthogonal.Transverse.mem`: a strict transverse crossing belongs to both full segments.
-/

public section

namespace PushPuzzle.Orthogonal

open Cslib Cslib.Orthogonal

/-- Strict transversality supplies membership in both continuous segments. -/
theorem Transverse.mem {a b c d : Point} {p : ℝ × ℝ} (h : Transverse a b c d p) :
    p ∈ segment a b ∧ p ∈ segment c d := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, by'⟩
  rcases c with ⟨cx, cy⟩
  rcases d with ⟨dx, dy⟩
  rcases h with ⟨rfl, rfl, rfl, hx₀, hx₁, hy₀, hy₁⟩ |
    ⟨rfl, rfl, rfl, hx₀, hx₁, hy₀, hy₁⟩
  · constructor
    · apply mem_horizontal.mpr
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_uIcc]
      norm_cast
      omega
    · apply mem_vertical.mpr
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_uIcc]
      norm_cast
      omega
  · constructor
    · apply mem_vertical.mpr
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_uIcc]
      norm_cast
      omega
    · apply mem_horizontal.mpr
      refine ⟨rfl, ?_⟩
      simp only [Set.mem_uIcc]
      norm_cast
      omega

end PushPuzzle.Orthogonal

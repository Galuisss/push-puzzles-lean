/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Init
public import CslibFrontier.Foundations.Geometry.Orthogonal.Macrocell
public import CslibFrontier.Foundations.Geometry.Orthogonal.Scale
public import CslibFrontier.Foundations.Geometry.Orthogonal.Isolation
import Mathlib.Tactic.Linarith

/-!
# Placing integer routing sites at macrocell centers

For a local gadget radius `r`, dilation by `2(r+1)` followed by translation by `(r+1,r+1)` sends
each integer point to the center of its own radius-`r+1` macrocell. This fixes a uniform margin
between local gadget support and the cell boundary. All transformations act on actual route data.

## Main definitions

* `PushPuzzle.Orthogonal.CellScale.point`: the transformed integer site.
* `PushPuzzle.Orthogonal.CellScale.route`: uniform dilation and translation of a route.

## Main results

* `PushPuzzle.Orthogonal.CellScale.isSimple`: transformed routes preserve simplicity.
* `PushPuzzle.Orthogonal.CellScale.point_not_mem_cell`: other integer sites avoid each closed cell.
-/

public section

namespace PushPuzzle.Orthogonal.CellScale

open Cslib Cslib.Orthogonal

/-- The integer point becomes the center of its own macrocell. -/
@[expose] def point (r : ℕ) (p : Point) : Point :=
  cellOrigin (r + 1) p + ((r : ℤ) + 1, (r : ℤ) + 1)

/-- Scale the actual listed points and translate every integer site to its macrocell center. -/
@[expose] def route (r : ℕ) (q : Route) : Route :=
  translate ((r : ℤ) + 1, (r : ℤ) + 1) (dilateRoute (2 * (r + 1)) q)

/-- The transformed full support is the uniform affine image of the original support. -/
private theorem support_route (r : ℕ) (q : Route) : support (route r q) =
    (fun p : ℝ × ℝ => (2 * ((r : ℝ) + 1)) • p + ((r : ℝ) + 1, (r : ℝ) + 1)) '' support q := by
  rw [route, support_translate, support_dilateRoute, Set.image_image]
  simp only [realPoint, Int.cast_add, Int.cast_natCast,
    Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, Int.cast_one]

/-- Positive uniform dilation and translation preserve continuous simplicity. -/
theorem isSimple (r : ℕ) {q : Route} (hq : IsSimple q) : IsSimple (route r q) := by
  rw [route, isSimple_translate_iff, isSimple_dilateRoute_iff (by omega)]
  exact hq

/-- Every integer routing site is strictly inside its assigned macrocell. -/
private theorem point_mem_cell (r : ℕ) (p : Point) : realPoint (point r p) ∈ openCell (r + 1) p :=
  center_mem_openCell (by omega) p

/-- A different transformed integer site is outside the site's entire closed macrocell. -/
theorem point_not_mem_cell (r : ℕ) {p q : Point} (hpq : p ≠ q) :
    realPoint (point r p) ∉ closedCell (r + 1) q :=
  fun h => hpq (cell_eq_of_mem_open_closed (by omega) (point_mem_cell r p) h)

private theorem near_of_mem_cell (r : ℕ) {c : Point} {p : ℝ × ℝ}
    (h : (2 * ((r : ℝ) + 1)) • p + ((r : ℝ) + 1, (r : ℝ) + 1) ∈ closedCell (r + 1) c) :
    nearGridPoint c p := by
  simp only [closedCell, Set.mem_ofPred_eq, Prod.fst_add, Prod.snd_add, Prod.smul_fst,
    Prod.smul_snd, smul_eq_mul] at h
  push_cast at h
  have hr : (0 : ℝ) < (r : ℝ) + 1 := by positivity
  refine ⟨?_, ?_, ?_, ?_⟩ <;> nlinarith

/-- An orthogonal carrier entering a closed macrocell must pass through its original integer
site. The bound concerns every real point of every segment. -/
theorem gridPoint_mem_support_of_cell (r : ℕ) {q : Route} (hq : IsOrthogonal q)
    {c : Point} {p : ℝ × ℝ} (hp : p ∈ support (route r q))
    (hc : p ∈ closedCell (r + 1) c) : realPoint c ∈ support q := by
  rw [support_route] at hp
  obtain ⟨p, hp, rfl⟩ := hp
  exact gridPoint_mem_support_of_near hq hp (near_of_mem_cell r hc)

end PushPuzzle.Orthogonal.CellScale

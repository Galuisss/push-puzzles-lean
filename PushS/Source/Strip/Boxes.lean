/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Contact
public import PushS.Source.Orthogonal.CellScale

/-!
# Isolated macrocell boxes at actual crossings

Scale by `2(r+1)` and translate by `(r+1,r+1)`. Each original crossing site then lies at its
macrocell center. A closed crossing cell meets only its two participating carriers and avoids
all transformed source centers and bends. The side length depends only on the chosen local
radius, so the complete two-panel support windows are retained after this uniform transformation.

## Main results

* `PushPuzzle.NCL.Strip.Environment.crossing_cell_routes_eq`: the crossing box meets only its two carriers.
* `PushPuzzle.NCL.Strip.Environment.crossing_cell_avoids_points`: all listed centers and bends avoid that box.
-/

public section

namespace PushPuzzle.NCL.Strip.Environment

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- A real point in the transformed carrier and a closed crossing cell belongs to one of the
two participating carriers. -/
theorem crossing_cell_routes_eq (r : ℕ) {e f g : E} {d : Bool} {p z : ℝ × ℝ}
    (h : R.Crossing e f d p) (hz : z ∈ support (PushPuzzle.Orthogonal.CellScale.route r (R.route g)))
    (hc : z ∈ closedCell (r + 1) (R.crossingSite e f d)) : g = e ∨ g = f := by
  have hm := PushPuzzle.Orthogonal.CellScale.gridPoint_mem_support_of_cell r (R.route_orthogonal g) hz hc
  rw [← R.crossing_point h] at hm
  exact R.crossing_routes_eq h hm

/-- The entire closed crossing cell avoids all transformed listed centers and bends in the
environment. -/
theorem crossing_cell_avoids_points (r : ℕ) {e f g : E} {d : Bool} {p : ℝ × ℝ}
    (h : R.Crossing e f d p) {a : Point} (ha : a ∈ R.route g) :
    realPoint (PushPuzzle.Orthogonal.CellScale.point r a) ∉ closedCell (r + 1) (R.crossingSite e f d) := by
  apply PushPuzzle.Orthogonal.CellScale.point_not_mem_cell
  intro he
  exact R.crossing_not_points h ha ((R.crossing_point h).trans (congrArg realPoint he.symm))

end PushPuzzle.NCL.Strip.Environment

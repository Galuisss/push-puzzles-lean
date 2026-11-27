/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Planar.GridDrawing.UnitRoute
import all PushS.Source.Planar.GridDrawing.UnitRoute
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridDrawing.UnitRoute

/-!
# Row order of the actual normalized grid paths

The original grid paths use horizontal and downward vertical segments. Their explicit unit
subdivision preserves the row order, and cycle erasure retains a sublist of the same point list.

## Main results

* `PushPuzzle.NCL.GridRouting.Path.unitRoute_rows`: actual normalized routes never move upward.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib

private theorem walk_rows (a d : Orthogonal.Point) (hd : 0 ≤ d.2) (n : ℕ) :
    (∀ p ∈ Orthogonal.walk a d n, a.2 ≤ p.2) ∧
      (Orthogonal.walk a d n).Pairwise (fun p q => p.2 ≤ q.2) := by
  induction n generalizing a with
  | zero => simp [Orthogonal.walk]
  | succ n ih =>
    have ht := ih (a + d)
    have hh : ∀ p ∈ Orthogonal.walk (a + d) d n, a.2 ≤ p.2 := by
      intro p hp
      have hy := ht.1 p hp
      change a.2 + d.2 ≤ p.2 at hy
      omega
    simp only [Orthogonal.walk, List.mem_cons, List.pairwise_cons]
    exact ⟨fun p hp => hp.elim (fun h => h ▸ le_rfl) (hh p), hh, ht.2⟩

private theorem direction_rows {a b : Orthogonal.Point} (h : a.2 ≤ b.2) (hne : a ≠ b) :
    0 ≤ (Orthogonal.direction a b).2 := by
  rcases a with ⟨ax, ay⟩
  rcases b with ⟨bx, byy⟩
  simp only [ne_eq, Prod.mk.injEq, not_and_or] at hne
  unfold Orthogonal.direction
  split_ifs <;> dsimp only <;> omega

private theorem segmentWalk_rows (a b : Orthogonal.Point) (h : a.2 ≤ b.2) :
    (Orthogonal.segmentWalk a b).Pairwise (fun p q => p.2 ≤ q.2) := by
  by_cases he : a = b
  · subst b
    simp [Orthogonal.segmentWalk, Orthogonal.length, Orthogonal.walk]
  · exact (walk_rows _ _ (direction_rows h he) _).2

namespace GridRouting.Path

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridRouting Cslib.Complexity.NCL.GridRouting.Path

/-- The original segment-by-segment unit walk retains the grid path's actual row order. -/
private theorem unitWalk_rows {p q : GridRouting.Point} (P : Path p q) :
    (PushPuzzle.NCL.GridRouting.Path.unitWalk P).support.Pairwise (fun p q => p.2 ≤ q.2) := by
  induction P with
  | horizontal x x' y =>
    rw [unitWalk_horizontal_support]
    exact segmentWalk_rows _ _ (by rfl)
  | vertical x y y' h =>
    rw [unitWalk_vertical_support]
    apply segmentWalk_rows
    change (y : ℤ) ≤ y'
    exact_mod_cast h
  | @comp p q r P Q ihP ihQ =>
    rw [unitWalk_comp_support, List.pairwise_append]
    refine ⟨ihP, ihQ.tail, ?_⟩
    intro u hu v hv
    obtain ⟨x, hx, hpx⟩ := (PushPuzzle.NCL.GridRouting.Path.unitWalk_trace P) u hu
    obtain ⟨y, hy, hqy⟩ := (PushPuzzle.NCL.GridRouting.Path.unitWalk_trace Q) v (List.mem_of_mem_tail hv)
    have hxy : x.2 ≤ y.2 := (P.row_bounds hpx).2.trans (Q.row_bounds hqy).1
    rw [← hx, ← hy]
    change (x.2 : ℤ) ≤ y.2
    exact_mod_cast hxy

/-- Cycle erasure retains the actual row order in every original normalized grid route. -/
theorem unitRoute_rows {p q : GridRouting.Point} (P : Path p q) :
    P.unitRoute.Pairwise (fun p q => p.2 ≤ q.2) :=
  (unitWalk_rows P).sublist (unitRoute_sublist_unitWalk P)

end GridRouting.Path
end PushPuzzle.NCL

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.DrawingResources
import all CslibFrontier.Computability.Complexity.Problems.NCL.Planar.GridRouting
import Mathlib.Algebra.Order.Group.Nat

/-!
# Column bounds for the actual canonical layer routing

Use the existing `GridLayout.layer` algorithm at each layer. Its intermediate columns are the
sum of its endpoint columns plus a wire index, so bounded actual stack sizes give a fixed
quadratic column bound for every point of every full strand trace.

## Main definitions

* `Strip.Sweep.drawingWidth`: a uniform column budget for canonical bounded-width layers.

## Main results

* `PushPuzzle.NCL.GridLayout.layer_trace_column_le`: the actual layer algorithm keeps each full trace in bounds.
-/

public section

namespace PushPuzzle.NCL

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- A quadratic column budget for the actual two-band layer-routing algorithm. -/
@[expose] def Strip.Sweep.drawingWidth (n : ℕ) : ℕ :=
  4 * n + 4 + (2 * n * (4 * n + 4) + n + 4)

namespace GridRouting

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridRouting

private theorem route_column_le {m : ℕ} (source target : Fin m → ℕ)
    (hs : StrictMono source) (ht : StrictMono target) (i : Fin m) {p : Point}
    (hp : (route source target hs ht).Contains i p) :
    p.1 ≤ portBound source target + m + 1 := by
  have hs' : source i ≤ portBound source target :=
    List.le_sum_of_mem (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have ht' : target i ≤ portBound source target :=
    List.le_sum_of_mem (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i, rfl⟩))
  have hi := i.isLt
  simp only [OrderedRouting.Contains, route, Elbow.Contains] at hp
  rcases hp with (h | h | h) | ⟨_, (h | h | h)⟩ <;> omega

private theorem portBound_le {m n : ℕ} (source target : Fin m → ℕ) (hm : m ≤ n)
    (hs : ∀ i, source i ≤ 4 * n + 4) (ht : ∀ i, target i ≤ 4 * n + 4) :
    portBound source target ≤ 2 * n * (4 * n + 4) := by
  have hs' := List.sum_le_length_nsmul (List.ofFn source) (4 * n + 4) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact hs i)
  have ht' := List.sum_le_length_nsmul (List.ofFn target) (4 * n + 4) (by
    intro x hx
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact ht i)
  have hm' := Nat.mul_le_mul_right (4 * n + 4) hm
  simp only [portBound, List.sum_append, List.length_ofFn, nsmul_eq_mul, Nat.cast_id] at *
  rw [Nat.mul_assoc]
  omega

end GridRouting

namespace GridLayout

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridLayout GridRouting

private theorem columns_le {k a r n : ℕ} (h : k + a + r ≤ n) (i : Fin (k + a + r)) :
    columns k a r i ≤ 4 * n + 4 := by
  have hi := i.isLt
  simp only [columns]
  split_ifs <;> omega

private theorem middle_column_le {k a b r n : ℕ} (h : a + b = 3)
    (ha : k + a + r ≤ n) (hb : k + b + r ≤ n) {e : Strand k a b r} {p : Point}
    (hp : MiddleContains e p) : p.1 ≤ 4 * n + 4 := by
  rcases e with i | (e | j)
  · have hi := i.isLt
    simp only [MiddleContains] at hp
    omega
  · have hx := (GridStar.bounded h hp.2).1
    have hl := hp.1
    omega
  · have hj := j.isLt
    simp only [MiddleContains] at hp
    omega

/-- Every point of the actual canonical full layer trace has bounded column. -/
theorem layer_trace_column_le {k a b r n : ℕ} (h : a + b = 3)
    (ha : k + a + r ≤ n) (hb : k + b + r ≤ n) {e : Strand k a b r} {p : Point}
    (hp : (layer k a b r h).Trace e p) : p.1 ≤ Strip.Sweep.drawingWidth n := by
  have upperBound : portBound (fun i : Fin (k + a + r) => 4 * i.val) (columns k a r) ≤
      2 * n * (4 * n + 4) := portBound_le _ _ ha
        (fun i => by have := i.isLt; omega) (fun i => columns_le ha i)
  have lowerBound : portBound (columns k b r) (fun i : Fin (k + b + r) => 4 * i.val) ≤
      2 * n * (4 * n + 4) := portBound_le _ _ hb
        (fun i => columns_le hb i) (fun i => by have := i.isLt; omega)
  rcases hp with ⟨i, _, hp⟩ | ⟨_, hp⟩ | ⟨_, j, _, hp⟩
  · have hx := route_column_le _ _
      (fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide))
      (columns_strictMono k a r (by omega)) i hp
    dsimp only [Strip.Sweep.drawingWidth]
    omega
  · have hx := middle_column_le h ha hb hp
    dsimp only [Strip.Sweep.drawingWidth]
    omega
  · have hx := route_column_le _ _ (columns_strictMono k b r (by omega))
      (fun _ _ h => Nat.mul_lt_mul_of_pos_left h (by decide)) j hp
    dsimp only [Strip.Sweep.drawingWidth]
    omega

end GridLayout
end PushPuzzle.NCL

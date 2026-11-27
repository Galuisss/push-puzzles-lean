/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Init
public import Mathlib.Data.List.Pairwise
public import Mathlib.Data.List.Range

/-!
# Actual consecutive scan-stage blocks

Emit each scan position once per vertex of its actual local implementation. Empty local blocks
contribute no vertices. The resulting stage list is sorted, and each stage occurs exactly its
own local block size times.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.stageBlocks`: the actual repeated chronological stage blocks.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.stageBlocks_sorted`: actual compilation order is monotone in scan stage.
* `PushPuzzle.NCL.Strip.Sweep.count_stageBlocks`: exact actual local-block multiplicity.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib

/-- Repeat each actual stage by the number of vertices emitted at that stage. -/
@[expose] def stageBlocks (count : ℕ → ℕ) (n : ℕ) : List ℕ :=
  (List.range n).flatMap (fun i => List.replicate (count i) i)

/-- Every actual emitted stage precedes the end of the actual finite scan prefix. -/
private theorem mem_stageBlocks_lt (count : ℕ → ℕ) (n : ℕ) {r : ℕ}
    (hr : r ∈ stageBlocks count n) : r < n := by
  obtain ⟨i, hi, hm⟩ := List.mem_flatMap.mp hr
  have he := (List.mem_replicate.mp hm).2
  simpa only [he] using List.mem_range.mp hi

/-- The actual compilation-order stages are monotone, including empty local implementations. -/
theorem stageBlocks_sorted (count : ℕ → ℕ) (n : ℕ) :
    (stageBlocks count n).Pairwise (· ≤ ·) := by
  induction n with
  | zero => simp [stageBlocks]
  | succ n ih =>
    simp only [stageBlocks, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil]
    rw [List.pairwise_append]
    refine ⟨ih, List.pairwise_replicate.mpr (Or.inr (le_refl _)), ?_⟩
    intro a ha b hb
    have hn := mem_stageBlocks_lt count n ha
    have he := (List.mem_replicate.mp hb).2
    omega

/-- Each actual stage occurs exactly as many times as its own actual local implementation size.
-/
theorem count_stageBlocks (count : ℕ → ℕ) (n r : ℕ) :
    (stageBlocks count n).count r = if r < n then count r else 0 := by
  induction n with
  | zero => simp [stageBlocks]
  | succ n ih =>
    simp only [stageBlocks, List.range_succ, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.count_append]
    change (stageBlocks count n).count r + (List.replicate (count n) n).count r = _
    rw [ih, List.count_replicate]
    by_cases he : n = r
    · subst r
      simp
    · have hn : (r < n + 1) = (r < n) := propext (by omega)
      simp [he, hn]

end PushPuzzle.NCL.Strip.Sweep

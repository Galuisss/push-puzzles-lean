/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ScanColumns
public import Push.ScanEmbedding
public import Push.ScanComposition
import all Push.Scan

/-! Parallel destructive reads commute, including repeated requests on the same lane. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

variable {w h : ℕ}

/-- Consecutive reads from the same side and lane add their literal quotas. -/
theorem read_bind_add (side : Direction) (lane q r : ℕ) (E : Finset (Cell w h)) :
    ((Instruction.read side lane q).eval E).bind ((Instruction.read side lane r).eval) =
      (Instruction.read side lane (q + r)).eval E := (consume_add _ _ _ _).symm

private theorem read_distinct_commute (side : Direction) (left right q r : ℕ) (hne : left ≠ right)
    (E : Finset (Cell w h)) :
    ((Instruction.read side left q).eval E).bind ((Instruction.read side right r).eval) =
      ((Instruction.read side right r).eval E).bind ((Instruction.read side left q).eval) := by
  let A := E.filter fun p => side.lane p = left
  let R := E.filter fun p => side.lane p ≠ left
  have hE : E = A ∪ R := by ext p; simp only [A, R, Finset.mem_union, Finset.mem_filter]; tauto
  have hA : (Instruction.read side left q).eval E =
      ((Instruction.read side left q).eval A).map (· ∪ R) := by
    rw [hE]
    apply Instruction.eval_union
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have hR : (Instruction.read side right r).eval E =
      ((Instruction.read side right r).eval R).map (· ∪ A) := by
    rw [hE, Finset.union_comm]
    apply Instruction.eval_union
    intro p hp
    have hx := (Finset.mem_filter.mp hp).2
    change side.lane p ≠ right
    omega
  rw [hA, hR]
  cases ha : (Instruction.read side left q).eval A with
  | none =>
    cases hr : (Instruction.read side right r).eval R with
    | none => rfl
    | some V =>
      simp only [Option.map_none, Option.bind_none, Option.map_some, Option.bind_some]
      rw [Finset.union_comm V A, Instruction.eval_union]
      · rw [ha]; rfl
      · intro p hp
        exact (Finset.mem_filter.mp (Instruction.eval_subset hr hp)).2
  | some U =>
    have hU : ∀ p ∈ U, side.lane p ≠ right := by
      intro p hp
      have hx := (Finset.mem_filter.mp (Instruction.eval_subset ha hp)).2
      omega
    cases hr : (Instruction.read side right r).eval R with
    | none =>
      simp only [Option.map_some, Option.bind_some, Option.map_none, Option.bind_none]
      rw [Finset.union_comm U R, Instruction.eval_union]
      · rw [hr]; rfl
      · exact hU
    | some V =>
      simp only [Option.map_some, Option.bind_some]
      rw [Finset.union_comm U R, Instruction.eval_union, Finset.union_comm V A, Instruction.eval_union]
      · rw [ha, hr]
        simp only [Option.map_some, Finset.union_comm]
      · intro p hp
        exact (Finset.mem_filter.mp (Instruction.eval_subset hr hp)).2
      · exact hU

/-- Same-direction read requests commute on their exact Option-valued remainder, even on a repeated lane. -/
theorem read_bind_commute (side : Direction) (left right q r : ℕ) (E : Finset (Cell w h)) :
    ((Instruction.read side left q).eval E).bind ((Instruction.read side right r).eval) =
      ((Instruction.read side right r).eval E).bind ((Instruction.read side left q).eval) := by
  by_cases he : left = right
  · subst right
    rw [read_bind_add, read_bind_add, Nat.add_comm q r]
  · exact read_distinct_commute side left right q r he E

end PushPuzzle.Push.Scan

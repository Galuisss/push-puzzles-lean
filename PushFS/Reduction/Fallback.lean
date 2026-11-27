/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.StaticTracks
import Mathlib.Tactic.FinCases

/-!
# A certified rejecting instance

The total reduction uses this board for malformed source data. Its two adjacent
boxes lie in one straight SCC, while its two target cells are separated. The
SCC transfer theorem rules out every solution, at every push cap.
-/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction


/-- A six-cell corridor with adjacent starting boxes and separated goals. -/
abbrev reject : Instance where
  width := 6
  height := 1
  board := ⟨∅, {(1, 0), (4, 0)}⟩
  initial := ⟨(0, 0), {(2, 0), (3, 0)}⟩
  goals_floor := by decide
  initial_valid := by unfold State.Valid; decide
  boxes_eq_goals := by decide

private def source : Fin 2 ↪ Cell 6 1 where
  toFun i := (⟨i.val + 2, by omega⟩, 0)
  inj' := by
    intro i j he
    have hv := congrArg (fun p : Cell 6 1 => p.1.val) he
    apply Fin.ext
    change i.val + 2 = j.val + 2 at hv
    omega

private def target : Fin 2 ↪ Cell 6 1 where
  toFun i := (⟨1 + 3 * i.val, by omega⟩, 0)
  inj' := by
    intro i j he
    have hv := congrArg (fun p : Cell 6 1 => p.1.val) he
    apply Fin.ext
    change 1 + 3 * i.val = 1 + 3 * j.val at hv
    omega

private def matching : SlotMatching reject (Fin 2) where
  source := source
  target := target
  source_image := by decide
  target_image := by decide
  connected := by
    intro i
    fin_cases i
    all_goals
      constructor <;> exact .single (by unfold Displacement; decide)

private def boundary (p : Cell 6 1) : Bool := decide (p.1.val = 0 ∨ p.1.val = 5)

private def tracks : StaticTracks reject Bool where
  name := boundary
  level b := if b then 1 else 0
  displacement := by unfold Displacement; decide
  linear _ _ := Or.inr (fun _ _ => Subsingleton.elim _ _)
  separated := by decide

/-- The rejecting board satisfies the actual semantic C1–C3 certificate. -/
theorem reject_certificate : Certificate reject := tracks.certificate matching

/-- The rejecting board has no solution for any finite or unlimited push cap. -/
theorem reject_not_solvable (cap : Option ℕ) : ¬reject.Solvable cap := by
  intro h
  obtain ⟨final, hr, hsol⟩ := Instance.solvable_unlimited h
  apply reject_certificate.no_adjacentPair .refl hr hsol
  refine ⟨(2, 0), by decide, (3, 0), by decide, rfl, ?_, .east, by decide⟩
  apply component_eq_iff.mpr
  constructor
  · exact .single (by unfold Displacement; decide)
  · exact .single (by unfold Displacement; decide)

end PushPuzzle.PushFS.Reduction

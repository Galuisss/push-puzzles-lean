/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Scan

/-! Sequential composition of destructive scan programs. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

variable {w h : ℕ}

/-- Concatenation executes the second program on the first program's exact remainder. -/
theorem eval_append (first second : List (Instruction w h)) (E : Finset (Cell w h)) :
    eval (first ++ second) E = (eval first E).bind (eval second) := by
  induction first generalizing E with
  | nil => rfl
  | cons i rest ih => simp only [List.cons_append, eval, Option.bind_assoc, ih]

/-- Acceptance of a concatenation factors through its actual intermediate bitmap. -/
theorem accepts_append_iff (first second : List (Instruction w h)) (E : Finset (Cell w h)) :
    Accepts (first ++ second) E ↔ ∃ F, eval first E = some F ∧ Accepts second F := by
  simp only [Accepts, eval_append, Option.bind_eq_some_iff]
  constructor
  · rintro ⟨G, F, hF, hG⟩
    exact ⟨F, hF, G, hG⟩
  · rintro ⟨F, hF, G, hG⟩
    exact ⟨G, F, hF, hG⟩

end PushPuzzle.Push.Scan

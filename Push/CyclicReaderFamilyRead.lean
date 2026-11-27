/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderFamily

/-! Exact first-read data, actual lane bounds, and budgets from one fixed-shape reader family. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader.Family

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}

/-- The computed sparse requests of this family's first future read block. -/
def requests (F : Family α enc shapes) (a : α) : List (ℕ × ℕ) := firstRequests (F.rounds a)

/-- The computed compact blocks following the first future block. -/
def remaining (F : Family α enc shapes) (a : α) : List Round := (F.rounds a).tail

@[fun_prop] theorem requests_polyTime (F : Family α enc shapes) :
    ComputableInPolyTime F.requests enc Scan.encRequests := firstRequests_polyTime.comp F.rounds_polyTime

@[fun_prop] theorem remaining_polyTime (F : Family α enc shapes) :
    ComputableInPolyTime F.remaining enc encRounds := by
  have hb := F.rounds_polyTime
  unfold remaining encRounds
  fun_prop

variable (F : Family α enc ((true, .west) :: shapes))

/-- A fixed leading west-read shape determines the actual computed first block. -/
theorem read_decomposition (a : α) :
    F.rounds a = .read .west (F.requests a) :: F.remaining a ∧
      (F.remaining a).map Round.shape = shapes := read_cons_of_shapes _ _ _ (F.shapes_eq a)

/-- Every actual first request names an original source row. -/
theorem requests_bounded (a : α) : ∀ request ∈ F.requests a, request.1 < (F.reader a).height := by
  intro request hr
  apply F.bounded a (.read .west request.1 request.2)
  rw [(F.read_decomposition a).1]
  change Scan.Instruction.read .west request.1 request.2 ∈
    Scan.lines .west (F.requests a) ++ instructions (F.remaining a)
  exact List.mem_append_left _ (List.mem_map.mpr ⟨request, hr, rfl⟩)

/-- Every future instruction retains the same actual source-lane bound. -/
theorem remaining_bounded (a : α) :
    ∀ i ∈ instructions (F.remaining a), Cyclic.SourceBounded (F.reader a) i := by
  intro i hi
  apply F.bounded a i
  rw [(F.read_decomposition a).1]
  exact List.mem_append_right _ hi

/-- The complete real program budget also holds in its literal read-cons decomposition. -/
theorem read_budget (a : α) :
    Cyclic.Budget (F.reader a) (.read .west (F.requests a) :: F.remaining a) := by
  rw [← (F.read_decomposition a).1]
  exact F.budget a

/-- The sparse first block's exact dense vector fits the actual current source inventory. -/
theorem requests_budget (a : α) :
    (Cyclic.rowQuotas (F.reader a) (F.requests a)).sum ≤ (F.reader a).sourceHoles :=
  Cyclic.rowQuotas_budget _ _ _ (F.requests_bounded a) (F.read_budget a)

end PushPuzzle.Push.CyclicReader.Family

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderFamilyRead

/-! One ordinary physical peel preserves every certified fixed-shape polynomial-time reader family. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicReader.Family

open PushFS PushS AcceptanceProgram Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}
  (F : Family α enc ((true, .west) :: (true, .north) :: shapes))

/-- Peel the current first source read, retaining the exact transformed program and actual source bitmap. -/
def normal : Family α enc (CyclicSchedule.normalSuffix ((true, .west) :: (true, .north) :: shapes)) where
  reader a := Cyclic.nextInput (F.reader a) (Cyclic.rowQuotas (F.reader a) (F.requests a))
    (Cyclic.rowQuotas_length _ _) (F.requests_budget a)
  rounds a := Cyclic.nextRounds (F.reader a) (F.remaining a)
  reader_polyTime := Cyclic.reader_base_west_input_polyTime F.reader_polyTime F.requests_polyTime F.requests_budget
  rounds_polyTime := Cyclic.nextRounds_polyTime F.reader_polyTime F.remaining_polyTime
  shapes_eq a := by
    rw [Cyclic.nextRounds_shapes, (F.read_decomposition a).2]
    rfl
  bounded a i hi := (Cyclic.sourceBounded_iff_bounded _ i).mpr
    (Cyclic.nextRounds_bounded (F.reader a) (F.remaining a) (F.remaining_bounded a) i hi)
  budget a := Cyclic.round_step_budget (F.reader a) (F.requests a) (F.requests_bounded a)
    (F.remaining a) (F.read_budget a)
  extra_zero _ := rfl
  erase_ready a _ := Cyclic.nextInput_height_le_quota _ _ _ _ (by rw [F.extra_zero a]; omega)

/-- The ordinary transformed family has exactly the same complete accepted source computations. -/
theorem normal_language_iff (a : α) :
    Cyclic.Language (F.normal.reader a) (F.normal.rounds a) ↔ Cyclic.Language (F.reader a) (F.rounds a) := by
  have he := Cyclic.round_step_language_iff (F.reader a) (F.requests a) (F.requests_bounded a)
    (F.remaining a) (F.remaining_bounded a) (F.requests_budget a)
  rw [← (F.read_decomposition a).1] at he
  exact he

end PushPuzzle.Push.CyclicReader.Family

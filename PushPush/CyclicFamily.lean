/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderSource

/-! Standard polynomial-time families for successive maximum-sliding read rounds. -/

@[expose] public section
namespace PushPuzzle.PushPush.CyclicReader

open PushFS (Direction)
open Push.AcceptanceProgram
open Push.CyclicReader

variable {α : Type} {enc : α ↪ List Bool} {shapes : List (Bool × Direction)}

/-- Attach one real reader and dock, then turn the unchanged future read blocks. -/
def advance (F : Family α enc ((true, .west) :: shapes)) :
    Family α enc (Push.CyclicSchedule.turnShapes shapes) where
  reader a := Push.Cyclic.nextInput (F.reader a) (Push.Cyclic.rowQuotas (F.reader a) (F.requests a))
    (Push.Cyclic.rowQuotas_length _ _) (F.requests_budget a)
  rounds a := Push.Cyclic.nextRounds (F.reader a) (F.remaining a)
  reader_polyTime := Push.Cyclic.reader_base_west_input_polyTime F.reader_polyTime
    F.requests_polyTime F.requests_budget
  rounds_polyTime := Push.Cyclic.nextRounds_polyTime F.reader_polyTime F.remaining_polyTime
  shapes_eq a := by
    rw [Push.Cyclic.nextRounds_shapes, (F.read_decomposition a).2]
    rfl
  bounded a i hi := (Push.Cyclic.sourceBounded_iff_bounded _ i).mpr
    (Push.Cyclic.nextRounds_bounded (F.reader a) (F.remaining a) (F.remaining_bounded a) i hi)
  budget a := Push.Cyclic.round_step_budget (F.reader a) (F.requests a) (F.requests_bounded a)
    (F.remaining a) (F.read_budget a)
  extra_zero _ := rfl
  erase_ready a _ := Push.Cyclic.nextInput_height_le_quota _ _ _ _ (by rw [F.extra_zero a]; omega)

/-- Use the source family's literal rounds and dense first vector. -/
def direct (F : SourceFamily α enc shapes) : Family α enc ((true, .west) :: shapes) where
  reader := F.reader
  rounds := F.rounds
  reader_polyTime := Push.ColumnScan.Input.ofInstance_polyTime F.source_polyTime F.firstQuotas_polyTime
    F.firstQuotas_length F.firstQuotas_budget
  rounds_polyTime := F.rounds_polyTime
  shapes_eq := F.shapes_eq
  bounded a i hi := (Push.Cyclic.sourceBounded_iff_bounded _ i).mpr (F.rounds_bounded a i hi)
  budget a := by
    change (F.firstQuotas a).sum + Push.Scan.quota
      (instructions (w := (F.source a).width) (h := (F.source a).height) (F.rounds a)) ≤
        (PushS.holes (F.source a).initial).card
    rw [F.firstQuotas_sum a]
    exact F.budget a
  extra_zero _ := rfl
  erase_ready a _ := by
    change (F.source a).height ≤ (F.firstQuotas a).sum
    rw [F.firstQuotas_sum a]
    exact F.first_height a

end PushPuzzle.PushPush.CyclicReader

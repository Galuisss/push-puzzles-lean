/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicReaderFamily

/-! Standard PT padding of actual compact programs with a fixed finite read/clear shape. -/

public section
namespace PushPuzzle.Push.CyclicSchedule

open PushFS AcceptanceProgram Turing.MultiTapeTM
open scoped PushPuzzle.Push.AcceptanceProgram

private theorem tail_shapes {rounds : List Round} {shape : Bool × Direction}
    {shapes : List (Bool × Direction)} (hs : rounds.map Round.shape = shape :: shapes) :
    rounds.tail.map Round.shape = shapes := by
  cases rounds with
  | nil => cases hs
  | cons block rest => exact (List.cons.inj hs).2

private theorem padFrom_cons_shape (side : Direction) {rounds : List Round} {shape : Bool × Direction}
    {shapes : List (Bool × Direction)} (hs : rounds.map Round.shape = shape :: shapes) :
    padFrom side rounds = padding side shape.2 ++ (rounds.headD (.read .west [])) ::
      padFrom (nextSide shape.2) rounds.tail := by
  cases rounds with
  | nil => cases hs
  | cons block rest =>
    simp only [padFrom, List.headD_cons, List.tail_cons]
    rw [(List.cons.inj hs).1]

/-- A fixed-shape program family computes its exact cyclic padding in standard polynomial time. -/
theorem padFrom_polyTime {α : Type} {enc : α ↪ List Bool} (side : Direction)
    (shapes : List (Bool × Direction)) {rounds : α → List Round}
    (hr : ComputableInPolyTime rounds enc encRounds)
    (hs : ∀ a, (rounds a).map Round.shape = shapes) :
    ComputableInPolyTime (fun a => padFrom side (rounds a)) enc encRounds := by
  induction shapes generalizing side rounds with
  | nil =>
    have hz : ∀ a, rounds a = [] := fun a => List.map_eq_nil_iff.mp (hs a)
    exact (ComputableInPolyTime.const ([] : List Round)).of_enc_eq (by
      intro a
      rw [hz a]
      rfl)
  | cons shape shapes ih =>
    have hhead : ComputableInPolyTime (fun a => (rounds a).headD (.read .west [])) enc encRound := by
      fun_prop
    have htail : ComputableInPolyTime (fun a => (rounds a).tail) enc encRounds := by fun_prop
    have hnext := ih (nextSide shape.2) htail (fun a => tail_shapes (hs a))
    have hrecipe : ComputableInPolyTime (fun a => padding side shape.2 ++
        (rounds a).headD (.read .west []) :: padFrom (nextSide shape.2) (rounds a).tail) enc encRounds := by
      unfold encRounds
      fun_prop
    exact hrecipe.of_enc_eq (fun a => congrArg encRounds (padFrom_cons_shape side (hs a)))

end PushPuzzle.Push.CyclicSchedule

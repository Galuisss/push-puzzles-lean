/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlWire

/-! Explicit row equalities for every control action from a working-column phase. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source.Control

variable {storage : Bool} {I : Instance}

/-- A working-column action retains the exact source row and original door/wire identity. -/
def WorkingNext (register : Fin I.doors.length → Register) (row : ℕ)
    (next : Control storage I) : Prop :=
  (∃ index : Fin (layout storage I).wires.length,
    row = (layout storage I).wires[index].source ∧ next = ⟨register, .wire index 0⟩) ∨
  (∃ door : Fin I.doors.length, ∃ incoming : Register,
    row = doorBase door.val + incoming.row ∧ register door ≠ incoming ∧
      next = ⟨Function.update register door incoming,
        .working (doorBase door.val + collisionRow (register door) incoming)⟩) ∨
  (∃ door : Fin I.doors.length, ∃ incoming : Register,
    row = doorBase door.val + incoming.row ∧ register door ≠ incoming ∧
      next = ⟨register, .working (doorBase door.val + collisionRow incoming (register door))⟩) ∨
  (∃ v j p, v < (labels I).length ∧ j < slots I ∧ p < slots I ∧
    row = inputRow I v j p ∧ upperUsed I v j = true ∧
      next = ⟨register, .working (upperRow I v j)⟩) ∨
  (∃ v j p, v < (labels I).length ∧ j < slots I ∧ p < slots I ∧
    row = inputRow I v j p ∧ lowerUsed I v j = true ∧
      next = ⟨register, .working (lowerRow I v j)⟩)

theorem Step.working_cases {register : Fin I.doors.length → Register} {row : ℕ}
    {next : Control storage I} (hs : Step ⟨register, .working row⟩ next) :
    WorkingNext register row next := by
  cases hs with
  | enterWire register index => exact Or.inl ⟨index, rfl, rfl⟩
  | moveStored register door incoming hne =>
    exact Or.inr (Or.inl ⟨door, incoming, rfl, hne, rfl⟩)
  | moveSignal register door incoming hne =>
    exact Or.inr (Or.inr (Or.inl ⟨door, incoming, rfl, hne, rfl⟩))
  | upper register v j p hv hj hp hused =>
    exact Or.inr (Or.inr (Or.inr (Or.inl ⟨v, j, p, hv, hj, hp, rfl, hused, rfl⟩)))
  | lower register v j p hv hj hp hused =>
    exact Or.inr (Or.inr (Or.inr (Or.inr ⟨v, j, p, hv, hj, hp, rfl, hused, rfl⟩)))

end PushPuzzle.PushPush.Doors.Source.Control

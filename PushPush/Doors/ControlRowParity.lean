/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlRows

/-! All emitted and invalid output rows are odd; every input slot is even. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

theorem roomBase_even (I : Instance) (v j : ℕ) : roomBase I v j % 2 = 0 := by
  simp [roomBase, chamberHeight, Nat.add_mod, Nat.mul_mod]

theorem inputRow_even (I : Instance) (v j p : ℕ) : inputRow I v j p % 2 = 0 := by
  simp [inputRow, Nat.add_mod, Nat.mul_mod, roomBase_even]

theorem registerRow_even (I : Instance) (door : Fin I.doors.length) (value : Register) :
    (doorBase door.val + value.row) % 2 = 0 := by
  cases value <;> simp [doorBase, Register.row, Nat.add_mod, Nat.mul_mod]

theorem LaunchRow.odd {I : Instance} {row : ℕ} (h : LaunchRow I row) : row % 2 = 1 := by
  rcases h with ⟨i, _, offset, ho, rfl⟩ | ⟨v, j, rfl | rfl⟩
  · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · simp [upperRow, Nat.add_mod, roomBase_even]
  · have hh := chamberHeight_ge I
    have hb := roomBase_even I v j
    have hc : chamberHeight I % 2 = 0 := by simp [chamberHeight, Nat.add_mod, Nat.mul_mod]
    unfold lowerRow
    omega

theorem TerminalPinRow.odd {I : Instance} {row : ℕ} (h : TerminalPinRow I row) : row % 2 = 1 := by
  rcases h with ⟨i, _, offset, ho, rfl⟩ | ⟨v, j, p, _, rfl⟩
  · rcases ho with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [doorBase, Nat.add_mod, Nat.mul_mod]
  · simp [Nat.add_mod, inputRow_even]

end PushPuzzle.PushPush.Doors.Source

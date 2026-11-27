/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlWorking

/-! Row addresses separate location inputs, door slots and collision outputs. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

@[simp] theorem register_row_mod_ten (value : Register) : value.row % 10 = 0 := by
  cases value <;> rfl

theorem landing_bounds (moving stationary : Room.Slot) :
    9 ≤ Room.landing moving stationary ∧ Room.landing moving stationary ≤ 81 := by
  have hs := Room.slot_row_bounds stationary
  have ha := Room.landing_adjacent moving stationary
  omega

private theorem landing_ne_register (moving stationary : Room.Slot) (value : Register) :
    Room.landing moving stationary ≠ value.row := by
  have hv := register_row_mod_ten value
  have hs : stationary.row % 10 = 0 := by cases stationary <;> rfl
  have ha := Room.landing_adjacent moving stationary
  intro he
  omega

theorem inputRow_not_launch (I : Instance) (v j p : ℕ) (hp : p < slots I) :
    ¬ LaunchRow I (inputRow I v j p) := by
  have hh := chamberHeight_ge I
  have ho : 10 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
  intro hl
  rcases hl with ⟨i, hi, offset, ha, he⟩ | ⟨v', j', he | he⟩
  · have ha' : offset < 90 := by simp only [DoorLaunchOffset] at ha; omega
    have hb := door_row_before I hi ha'
    unfold inputRow roomBase at he
    omega
  · have he' : chamberHeight I * (slots I * v + j) + (10 + 8 * p) =
        chamberHeight I * (slots I * v' + j') + 3 := by
      unfold inputRow upperRow roomBase at he
      omega
    have hu := row_address_injective ho (by omega) he'
    omega
  · have he' : chamberHeight I * (slots I * v + j) + (10 + 8 * p) =
        chamberHeight I * (slots I * v' + j') + (chamberHeight I - 3) := by
      unfold inputRow lowerRow roomBase at he
      omega
    have hu := row_address_injective ho (by omega) he'
    unfold chamberHeight at hu
    omega

theorem door_register_not_launch (I : Instance) (door : Fin I.doors.length)
    (value : Register) : ¬ LaunchRow I (doorBase door.val + value.row) := by
  have hr := Register.row_bounds value
  have hm := register_row_mod_ten value
  have hb := door_row_before I door.isLt (by omega : value.row < 90)
  have hh := chamberHeight_ge I
  intro hl
  rcases hl with ⟨i, hi, offset, ha, he⟩ | ⟨v, j, he | he⟩
  · have ha' : offset < 90 := by simp only [DoorLaunchOffset] at ha; omega
    have hu := row_address_injective (by omega : value.row < 90) ha'
      (show 90 * door.val + value.row = 90 * i + offset by simpa only [doorBase] using he)
    simp only [DoorLaunchOffset] at ha
    omega
  · unfold upperRow roomBase at he
    omega
  · unfold lowerRow roomBase at he
    omega

theorem inputRow_ne_door_register (I : Instance) (v j p : ℕ)
    (door : Fin I.doors.length) (value : Register) :
    inputRow I v j p ≠ doorBase door.val + value.row := by
  have hr := Register.row_bounds value
  have hb := door_row_before I door.isLt (by omega : value.row < 90)
  unfold inputRow roomBase
  omega

theorem door_register_injective (I : Instance) (first second : Fin I.doors.length)
    (left right : Register)
    (he : doorBase first.val + left.row = doorBase second.val + right.row) :
    first = second ∧ left = right := by
  have hl := Register.row_bounds left
  have hr := Register.row_bounds right
  have hu := row_address_injective (by omega : left.row < 90) (by omega : right.row < 90)
    (show 90 * first.val + left.row = 90 * second.val + right.row by simpa only [doorBase] using he)
  exact ⟨Fin.ext hu.1, Register.row_injective hu.2⟩

theorem inputRow_injective (I : Instance) {v j p v' j' p' : ℕ}
    (hj : j < slots I) (hj' : j' < slots I) (hp : p < slots I) (hp' : p' < slots I)
    (he : inputRow I v j p = inputRow I v' j' p') : v = v' ∧ j = j' ∧ p = p' := by
  have ho : 10 + 8 * p < chamberHeight I := by unfold chamberHeight; omega
  have ho' : 10 + 8 * p' < chamberHeight I := by unfold chamberHeight; omega
  have hu := room_row_injective I hj hj' ho ho' (show
      roomBase I v j + (10 + 8 * p) = roomBase I v' j' + (10 + 8 * p') by
    simpa only [inputRow, Nat.add_assoc] using he)
  exact ⟨hu.1, hu.2.1, by omega⟩

theorem result_ne_door_register (I : Instance) (door other : Fin I.doors.length)
    (moving stationary : Room.Slot) (value : Register) :
    doorBase door.val + Room.landing moving stationary ≠ doorBase other.val + value.row := by
  have hl := landing_bounds moving stationary
  have hr := Register.row_bounds value
  intro he
  have hu := row_address_injective (by omega : Room.landing moving stationary < 90)
    (by omega : value.row < 90) (show
      90 * door.val + Room.landing moving stationary = 90 * other.val + value.row by
      simpa only [doorBase] using he)
  exact landing_ne_register moving stationary value hu.2

theorem result_ne_inputRow (I : Instance) (door : Fin I.doors.length)
    (moving stationary : Room.Slot) (v j p : ℕ) :
    doorBase door.val + Room.landing moving stationary ≠ inputRow I v j p := by
  have hl := landing_bounds moving stationary
  have hb := door_row_before I door.isLt (by omega : Room.landing moving stationary < 90)
  unfold inputRow roomBase
  omega

end PushPuzzle.PushPush.Doors.Source

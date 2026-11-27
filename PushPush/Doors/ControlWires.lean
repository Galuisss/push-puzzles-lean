/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlLocal
public import PushPush.Doors.WireSourceMembers
import Mathlib.Data.List.GetD

/-! Literal source-wire membership and the original directed channel selected by a choice. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- Recover the original finite door index of a dense channel. -/
def channelDoor (I : Instance) (j : Fin (2 * I.doors.length)) : Fin I.doors.length :=
  ⟨j.val / 2, by have := j.isLt; omega⟩

theorem channel_eq (I : Instance) (j : Fin (2 * I.doors.length)) :
    channel I j.val = I.doors[channelDoor I j].tunnel (channelBit j.val) := by
  unfold channel
  have hi : j.val / 2 < I.doors.length := (channelDoor I j).isLt
  rw [List.getD_eq_getElem _ _ hi]
  rfl

/-- The original door index and Boolean channel in the dense tunnel list. -/
def channelIndex (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    Fin (2 * I.doors.length) := ⟨2 * door.val + (if bit then 1 else 0), by
      have := door.isLt
      cases bit <;> simp
      omega⟩

@[simp] theorem channelBit_channelIndex (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    channelBit (channelIndex I door bit).val = bit := by
  cases bit <;> simp [channelIndex, channelBit, Nat.add_mod]

@[simp] theorem channelDoor_channelIndex (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    channelDoor I (channelIndex I door bit) = door := by
  apply Fin.ext
  dsimp [channelDoor, channelIndex]
  cases bit <;> simp
  omega

@[simp] theorem channel_channelIndex (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    channel I (channelIndex I door bit).val = I.doors[door].tunnel bit := by
  simpa only [channelDoor_channelIndex, channelBit_channelIndex] using
    channel_eq I (channelIndex I door bit)

theorem arrival_channelIndex_source (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    (arrivalWire I (channelIndex I door bit).val).source =
      doorBase door.val + (if bit then 29 else 61) := by
  have hdoor := congrArg Fin.val (channelDoor_channelIndex I door bit)
  change (channelIndex I door bit).val / 2 = door.val at hdoor
  simp only [arrivalWire, channelBit_channelIndex, hdoor]

theorem arrival_channelIndex_target (I : Instance) (door : Fin I.doors.length) (bit : Bool) :
    (arrivalWire I (channelIndex I door bit).val).target =
      inputRow I (rank I (I.doors[door].tunnel bit).target) 0 (channelIndex I door bit).val := by
  simp only [arrivalWire, channel_channelIndex]

theorem upperRow_ne_door_register (I : Instance) (v j : ℕ)
    (door : Fin I.doors.length) (value : Register) :
    upperRow I v j ≠ doorBase door.val + value.row := by
  have hr := Register.row_bounds value
  have hb := door_row_before I door.isLt (by omega : value.row < 90)
  unfold upperRow roomBase
  omega

theorem lowerRow_ne_door_register (I : Instance) (v j : ℕ)
    (door : Fin I.doors.length) (value : Register) :
    lowerRow I v j ≠ doorBase door.val + value.row := by
  have hr := Register.row_bounds value
  have hb := door_row_before I door.isLt (by omega : value.row < 90)
  have hh := chamberHeight_ge I
  unfold lowerRow roomBase
  omega

end PushPuzzle.PushPush.Doors.Source

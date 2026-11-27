/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlRows

/-! Location-room choices and the two collision choices preserve the active source phase. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

theorem ControlPhase.junction_step {storage : Bool} {I : Instance} {source : State}
    (j p : ℕ) (hj : j < slots I) (hp : p < slots I) {next : Control storage I}
    (hs : Control.Step
      ⟨sourceRegisters I source, .working (inputRow I (rank I source.location) j p)⟩ next) :
    ControlPhase storage I source next := by
  rcases hs.working_cases with hw | hm | hm | hu | hl
  · obtain ⟨index, he, _⟩ := hw
    exact False.elim (inputRow_not_launch I _ _ _ hp
      (he ▸ wires_launch storage I (List.getElem_mem index.isLt)))
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (inputRow_ne_door_register I _ _ _ door value he)
  · obtain ⟨door, value, he, _⟩ := hm
    exact False.elim (inputRow_ne_door_register I _ _ _ door value he)
  · obtain ⟨v', j', p', _, hj', hp', he, hused, rfl⟩ := hu
    obtain ⟨hv, he_j, _⟩ := inputRow_injective I hj hj' hp hp' he
    subst v'
    subst j'
    exact .upper j hj hused
  · obtain ⟨v', j', p', _, hj', hp', he, hused, rfl⟩ := hl
    obtain ⟨hv, he_j, _⟩ := inputRow_injective I hj hj' hp hp' he
    subst v'
    subst j'
    exact .lower j hj hused

theorem ControlPhase.call_step {storage : Bool} {I : Instance} {source : State}
    (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
    (hentry : source.location = (I.doors[door].tunnel channel).source)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.call stored incoming)) {next : Control storage I}
    (hs : Control.Step
      ⟨sessionRegisters I source door stored, .working (doorBase door.val + incoming.row)⟩ next) :
    ControlPhase storage I source next := by
  rcases hs.working_cases with hw | hm | hm | hu | hl
  · obtain ⟨index, he, _⟩ := hw
    have hbad := door_register_not_launch I door (Register.ofSlot incoming)
    apply False.elim
    apply hbad
    rw [Register.row_ofSlot]
    rw [he]
    exact wires_launch storage I (List.getElem_mem index.isLt)
  · obtain ⟨other, value, he, _, rfl⟩ := hm
    have hid := door_register_injective I door other (Register.ofSlot incoming) value
      (by simpa only [Register.row_ofSlot] using he)
    have hother : other = door := hid.1.symm
    subst other
    have hvalue : value = Register.ofSlot incoming := hid.2.symm
    subst value
    simpa only [sessionRegisters_self, sessionRegisters_update, collisionRow_ofSlot, ite_true] using
      (ControlPhase.result (storage := storage) door channel stored incoming true hentry hsession)
  · obtain ⟨other, value, he, _, rfl⟩ := hm
    have hid := door_register_injective I door other (Register.ofSlot incoming) value
      (by simpa only [Register.row_ofSlot] using he)
    have hother : other = door := hid.1.symm
    subst other
    have hvalue : value = Register.ofSlot incoming := hid.2.symm
    subst value
    simpa only [sessionRegisters_self, collisionRow_ofSlot, Bool.false_eq_true, ite_false] using
      (ControlPhase.result (storage := storage) door channel stored incoming false hentry hsession)
  · obtain ⟨v, j, p, _, _, _, he, _⟩ := hu
    exact False.elim (inputRow_ne_door_register I v j p door (Register.ofSlot incoming)
      (by simpa only [Register.row_ofSlot] using he.symm))
  · obtain ⟨v, j, p, _, _, _, he, _⟩ := hl
    exact False.elim (inputRow_ne_door_register I v j p door (Register.ofSlot incoming)
      (by simpa only [Register.row_ofSlot] using he.symm))

end PushPuzzle.PushPush.Doors.Source

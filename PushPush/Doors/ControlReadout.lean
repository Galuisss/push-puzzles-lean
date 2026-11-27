/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlPhase

/-! A completed six-slot door session produces exactly one original source traversal. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

@[simp] theorem sessionRegisters_self (I : Instance) (source : State)
    (door : Fin I.doors.length) (stored : Room.Slot) :
    sessionRegisters I source door stored door = Register.ofSlot stored := by
  simp [sessionRegisters]

theorem sessionRegisters_stable (I : Instance) (source : State) (door : Fin I.doors.length) :
    sessionRegisters I source door (Room.stable (source.bits.getD door.val false)) =
      sourceRegisters I source := by
  funext i
  by_cases hi : i = door
  · subst i
    simp [sourceRegisters]
  · simp [sessionRegisters, hi]

theorem sessionRegisters_update (I : Instance) (source : State)
    (door : Fin I.doors.length) (stored incoming : Room.Slot) :
    Function.update (sessionRegisters I source door stored) door (Register.ofSlot incoming) =
      sessionRegisters I source door incoming := by
  funext i
  by_cases hi : i = door
  · subst i
    simp
  · simp [sessionRegisters, hi]

private theorem sourceRegisters_set (I : Instance) (source : State)
    (hvalid : source.Valid I.doors) (door : Fin I.doors.length) (value : Bool) (location : ℕ) :
    sourceRegisters I ⟨location, source.bits.set door.val value⟩ =
      Function.update (sourceRegisters I source) door (Register.stable value) :=
  congrArg Stock.register (Stock.ofBits_set I source.bits (0, 0) hvalid door value)

/-- The active physical register becomes the stable flipped source bit on every real exit. -/
theorem room_exit_source_step (I : Instance) (source : State) (hvalid : source.Valid I.doors)
    (door : Fin I.doors.length) (channel out : Bool) (stored : Room.Slot)
    (hentry : source.location = (I.doors[door].tunnel channel).source)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.exit out stored)) :
    ∃ next : State, SelfClosingDoor.Step I.doors source next ∧
      next.location = (I.doors[door].tunnel channel).target ∧
      sessionRegisters I source door stored = sourceRegisters I next := by
  obtain ⟨hold, _, hstored⟩ :=
    (Room.reachable_exit_iff (source.bits.getD door.val false) channel out stored).mp hsession
  let next : State :=
    ⟨(I.doors[door].tunnel channel).target, source.bits.set door.val (!channel)⟩
  refine ⟨next, ⟨hvalid, door, ?_, ?_⟩, rfl, ?_⟩
  · simpa only [hold] using hentry
  · change next = _
    simp only [hold]
    rfl
  · rw [hstored]
    change Function.update (sourceRegisters I source) door
      (Register.ofSlot (Room.stable (!channel))) = sourceRegisters I next
    rw [Register.ofSlot_stable]
    exact (sourceRegisters_set I source hvalid door (!channel) _).symm

end PushPuzzle.PushPush.Doors.Source

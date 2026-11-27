/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.MachineControl
public import PushPush.Doors.WireSourceUnique

/-! Source configurations and single-door sessions attached to the actual control phases. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

/-- The physical stable slots read the original source bits without relabelling doors. -/
def sourceRegisters (I : Instance) (source : State) : Fin I.doors.length → Register :=
  fun i => Register.stable (source.bits.getD i.val false)

/-- A single active door may be in one of its six intermediate slots. -/
def sessionRegisters (I : Instance) (source : State) (door : Fin I.doors.length)
    (stored : Room.Slot) : Fin I.doors.length → Register :=
  Function.update (sourceRegisters I source) door (Register.ofSlot stored)

@[simp] theorem stable_ne_erase (bit : Bool) : Register.stable bit ≠ .erase := by
  cases bit <;> decide

@[simp] theorem ofSlot_ne_erase (slot : Room.Slot) : Register.ofSlot slot ≠ .erase := by
  cases slot <;> decide

@[simp] theorem collisionRow_ofSlot (moving stationary : Room.Slot) :
    collisionRow (Register.ofSlot moving) (Register.ofSlot stationary) =
      Room.landing moving stationary := by
  simp only [collisionRow, Register.row_ofSlot, Room.landing]

/-- Until the original target has been reached, the unique signal is in a location room,
one original door session, or the wire leading to the next such input. -/
inductive ControlPhase (storage : Bool) (I : Instance) (source : State) :
    Control storage I → Prop
  | junction (j p : ℕ) (hj : j < slots I) (hp : p < slots I) :
      ControlPhase storage I source
        ⟨sourceRegisters I source, .working (inputRow I (rank I source.location) j p)⟩
  | upper (j : ℕ) (hj : j < slots I)
      (used : upperUsed I (rank I source.location) j = true) :
      ControlPhase storage I source
        ⟨sourceRegisters I source, .working (upperRow I (rank I source.location) j)⟩
  | lower (j : ℕ) (hj : j < slots I)
      (used : lowerUsed I (rank I source.location) j = true) :
      ControlPhase storage I source
        ⟨sourceRegisters I source, .working (lowerRow I (rank I source.location) j)⟩
  | junctionWire (index : Fin (layout storage I).wires.length) (corner : Fin 8)
      (j p : ℕ) (hj : j < slots I) (hp : p < slots I)
      (target : (layout storage I).wires[index].target =
        inputRow I (rank I source.location) j p) :
      ControlPhase storage I source ⟨sourceRegisters I source, .wire index corner⟩
  | call (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
      (entry : source.location = (I.doors[door].tunnel channel).source)
      (session : Room.Reachable
        (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming)) :
      ControlPhase storage I source
        ⟨sessionRegisters I source door stored, .working (doorBase door.val + incoming.row)⟩
  | result (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
      (keepIncoming : Bool)
      (entry : source.location = (I.doors[door].tunnel channel).source)
      (session : Room.Reachable
        (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming)) :
      ControlPhase storage I source
        ⟨sessionRegisters I source door (if keepIncoming then incoming else stored),
          .working (doorBase door.val + if keepIncoming then Room.landing stored incoming
            else Room.landing incoming stored)⟩
  | doorWire (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
      (index : Fin (layout storage I).wires.length) (corner : Fin 8)
      (entry : source.location = (I.doors[door].tunnel channel).source)
      (session : Room.Reachable
        (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
        (.call stored incoming))
      (target : (layout storage I).wires[index].target = doorBase door.val + incoming.row) :
      ControlPhase storage I source
        ⟨sessionRegisters I source door stored, .wire index corner⟩

theorem ControlPhase.register_ne_erase {storage : Bool} {I : Instance} {source : State}
    {C : Control storage I} (h : ControlPhase storage I source C) (i : Fin I.doors.length) :
    C.register i ≠ .erase := by
  cases h <;> simp [sourceRegisters, sessionRegisters, Function.update_apply] <;>
    split_ifs <;> simp

/-- The invariant records the same actual source path throughout each in-progress door call. -/
def Control.SourceSafe {storage : Bool} {I : Instance} (C : Control storage I) : Prop :=
  I ∈ SelfClosingDoor.Reachability ∨
    ∃ source, SelfClosingDoor.Reachable I.doors I.initial source ∧
      ControlPhase storage I source C

theorem Control.initial_sourceSafe (storage : Bool) (I : Instance) :
    (Control.initial storage I).SourceSafe := by
  apply Or.inr
  refine ⟨I.initial, .refl, ?_⟩
  have hr : sourceRegisters I I.initial = (Stock.initial storage I).register := by
    funext i
    exact Stock.ofBits_initial_register I (Stock.initial storage I).signal i
  rw [Control.initial, ← hr]
  exact ControlPhase.junction 0 (2 * I.doors.length) (slots_pos I) (by unfold slots; omega)

end PushPuzzle.PushPush.Doors.Source

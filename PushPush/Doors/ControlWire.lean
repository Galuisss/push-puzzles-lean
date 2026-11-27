/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ControlReadout

/-! Wire microsteps preserve the original source configuration and door session. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

namespace SignalPosition

end SignalPosition

theorem ControlPhase.junctionWire_step {storage : Bool} {I : Instance} {source : State}
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (j p : ℕ) (hj : j < slots I) (hp : p < slots I)
    (htarget : (layout storage I).wires[index].target = inputRow I (rank I source.location) j p)
    {next : Control storage I}
    (hs : Control.Step ⟨sourceRegisters I source, .wire index corner⟩ next) :
    ControlPhase storage I source next := by
  cases hs with
  | wire register index corner => exact .junctionWire index corner.succ j p hj hp htarget
  | leaveWire register index =>
    rw [htarget]
    exact .junction j p hj hp

theorem ControlPhase.doorWire_step {storage : Bool} {I : Instance} {source : State}
    (door : Fin I.doors.length) (channel : Bool) (stored incoming : Room.Slot)
    (index : Fin (layout storage I).wires.length) (corner : Fin 8)
    (hentry : source.location = (I.doors[door].tunnel channel).source)
    (hsession : Room.Reachable
      (.call (Room.stable (source.bits.getD door.val false)) (Room.check channel))
      (.call stored incoming))
    (htarget : (layout storage I).wires[index].target = doorBase door.val + incoming.row)
    {next : Control storage I}
    (hs : Control.Step ⟨sessionRegisters I source door stored, .wire index corner⟩ next) :
    ControlPhase storage I source next := by
  cases hs with
  | wire register index corner =>
    exact .doorWire door channel stored incoming index corner.succ hentry hsession htarget
  | leaveWire register index =>
    rw [htarget]
    exact .call door channel stored incoming hentry hsession

end PushPuzzle.PushPush.Doors.Source

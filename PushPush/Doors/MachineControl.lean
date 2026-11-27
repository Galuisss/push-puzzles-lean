/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.MachineStateUpdate
public import PushPush.Doors.ForwardCollision

/-! The explicit chamber-and-wire control machine underlying a physical source board. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

/-- A signal is on the working column or at one of the eight corners of one original wire. -/
inductive SignalPosition (storage : Bool) (I : Instance)
  | working (row : ℕ)
  | wire (index : Fin (layout storage I).wires.length) (corner : Fin 8)

namespace SignalPosition

/-- The complete physical coordinate of the named signal phase. -/
def point {storage : Bool} {I : Instance} : SignalPosition storage I → ℕ × ℕ
  | .working row => ((layout storage I).rackX - 1, row + (layout storage I).shift)
  | .wire index corner =>
      ((layout storage I).wirePath index.val (layout storage I).wires[index]).getD corner.val (0, 0)

@[simp] theorem point_working (storage : Bool) (I : Instance) (row : ℕ) :
    (working (storage := storage) (I := I) row).point =
      ((layout storage I).rackX - 1, row + (layout storage I).shift) := rfl

@[simp] theorem point_wire_start (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length) :
    (wire index 0).point =
      (working (storage := storage) (I := I) (layout storage I).wires[index].source).point := by
  simp [point, Layout.wirePath]

@[simp] theorem point_wire_end (storage : Bool) (I : Instance)
    (index : Fin (layout storage I).wires.length) :
    (wire index 7).point =
      (working (storage := storage) (I := I) (layout storage I).wires[index].target).point := by
  simp [point, Layout.wirePath]

end SignalPosition

/-- One physical register per original door together with the signal's control phase. -/
structure Control (storage : Bool) (I : Instance) where
  /-- Current stored slots, retaining the source door identities. -/
  register : Fin I.doors.length → Register
  /-- The signal's current chamber row or original wire corner. -/
  signal : SignalPosition storage I

namespace Control

variable {storage : Bool} {I : Instance}

/-- Forget only the signal-phase name, preserving every physical box coordinate. -/
def stock (C : Control storage I) : Stock I := ⟨C.register, C.signal.point⟩

/-- The original source bits and the private starting input. -/
def initial (storage : Bool) (I : Instance) : Control storage I :=
  ⟨(Stock.initial storage I).register, .working (layout storage I).launch⟩

/-- The common terminal register inventory and signal row. -/
def terminal (storage : Bool) (I : Instance) : Control storage I :=
  ⟨(Stock.terminal storage I).register, .working (layout storage I).stop⟩

@[simp] theorem stock_initial (storage : Bool) (I : Instance) :
    (initial storage I).stock = Stock.initial storage I := rfl

@[simp] theorem stock_terminal (storage : Bool) (I : Instance) :
    (terminal storage I).stock = Stock.terminal storage I := rfl

/-- Safe signal motion: wire corners, either collision choice, and actual junction exits. -/
inductive Step : Control storage I → Control storage I → Prop
  | enterWire (register : Fin I.doors.length → Register)
      (index : Fin (layout storage I).wires.length) :
      Step ⟨register, .working (layout storage I).wires[index].source⟩
        ⟨register, .wire index 0⟩
  | wire (register : Fin I.doors.length → Register)
      (index : Fin (layout storage I).wires.length) (corner : Fin 7) :
      Step ⟨register, .wire index corner.castSucc⟩ ⟨register, .wire index corner.succ⟩
  | leaveWire (register : Fin I.doors.length → Register)
      (index : Fin (layout storage I).wires.length) :
      Step ⟨register, .wire index 7⟩
        ⟨register, .working (layout storage I).wires[index].target⟩
  | moveStored (register : Fin I.doors.length → Register) (i : Fin I.doors.length)
      (incoming : Register) (different : register i ≠ incoming) :
      Step ⟨register, .working (doorBase i.val + incoming.row)⟩
        ⟨Function.update register i incoming,
          .working (doorBase i.val + collisionRow (register i) incoming)⟩
  | moveSignal (register : Fin I.doors.length → Register) (i : Fin I.doors.length)
      (incoming : Register) (different : register i ≠ incoming) :
      Step ⟨register, .working (doorBase i.val + incoming.row)⟩
        ⟨register, .working (doorBase i.val + collisionRow incoming (register i))⟩
  | upper (register : Fin I.doors.length → Register) (v j p : ℕ)
      (location : v < (labels I).length) (candidate : j < slots I) (input : p < slots I)
      (used : upperUsed I v j = true) :
      Step ⟨register, .working (inputRow I v j p)⟩ ⟨register, .working (upperRow I v j)⟩
  | lower (register : Fin I.doors.length → Register) (v j p : ℕ)
      (location : v < (labels I).length) (candidate : j < slots I) (input : p < slots I)
      (used : lowerUsed I v j = true) :
      Step ⟨register, .working (inputRow I v j p)⟩ ⟨register, .working (lowerRow I v j)⟩

/-- Finite safe chamber-and-wire executions. -/
abbrev Reachable := Relation.ReflTransGen (@Step storage I)

end Control
end PushPuzzle.PushPush.Doors.Source

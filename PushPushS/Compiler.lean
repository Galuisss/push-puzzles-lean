/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Basic
public import PushPush.Doors.CompilerInstance

/-! The exact-storage door compiler, including its state-independent cleanup chain. -/

@[expose] public section
namespace PushPuzzle.PushPushS

open Cslib.Complexity Turing.MultiTapeTM

/-- Compile a door network to its explicit wall-free exact-storage puzzle. -/
def compile (I : SelfClosingDoor.Instance) : Instance := PushPush.Doors.Source.puzzle true I

/-- The full finite board is emitted by a standard polynomial-time machine. -/
@[fun_prop] theorem compile_polyTime :
    ComputableInPolyTime compile SelfClosingDoor.encInstance encoding :=
  PushPush.Doors.Source.puzzle_polyTime true

end PushPuzzle.PushPushS

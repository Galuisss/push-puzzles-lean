/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPushS.Compiler
public import PushPush.Doors.ForwardPhysical

/-! Exact storage after physical source simulation and state-independent register cleanup. -/

public section
namespace PushPuzzle.PushPushS

open Cslib.Complexity

/-- Every YES self-closing-door network has a full physical exact-storage solution. -/
theorem compile_forward (I : SelfClosingDoor.Instance)
    (hs : I ∈ SelfClosingDoor.Reachability) : Instance.Solvable (compile I) :=
  PushPush.Doors.Source.physical_storage_forward I hs

end PushPuzzle.PushPushS

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.FullGateRawLabels

/-! Canonical phase assignments on the fixed genuine primitive identities of a complete gate. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets
set_option maxRecDepth 65536

def withFlags (g : GateTileState) (a b : Gates.Signals) : GateTileState :=
  {g with core:={g.core with initial:=a,target:=b}}

end PushPuzzle.PushFS.Reduction.GateTileRouting

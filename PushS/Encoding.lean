/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushS.Basic
public import PushFS.Encoding

/-! The common dense rectangle encoding restricted to wall-free instances. -/

@[expose] public section
namespace PushPuzzle.PushS


/-- Unary dimensions and row-major flags; every fixed-wall flag is false. -/
def encoding : Instance ↪ List Bool :=
  (⟨Instance.toInstance, Instance.toInstance_injective⟩ : Instance ↪ PushFS.Instance).trans
    PushFS.encoding

end PushPuzzle.PushS

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Reduction.GateTileRouting
public import PushFS.Reduction.TranslateAtlas

/-! The actual four-piece buffered core, placed in its physical annular rectangle. -/

@[expose] public section

namespace PushPuzzle.PushFS.Reduction.GateTileRouting


open Gadgets Turing.MultiTapeTM ComputableInPolyTime

set_option maxRecDepth 65536

theorem buffer_fitX (kind : Bool) : (bufferOffset kind).1+4703≤200007 := by cases kind <;> decide +kernel
theorem buffer_fitY (kind : Bool) : (bufferOffset kind).2+4739≤198068 := by cases kind <;> decide +kernel

/-- Every physical core, buffer, flip and long-lead identity at its actual annular position. -/
def bufferAtlas (g : GateTileState) : StorageAtlas 4 200007 198068 (GateLead.Labels g.core.isAND 2301) :=
  (GateLead.atlas g.core.isAND 2301 (by omega) g.core.initial g.core.target).translate
    (bufferOffset g.core.isAND).1 (bufferOffset g.core.isAND).2
    (buffer_fitX g.core.isAND) (buffer_fitY g.core.isAND)

/-- The exact sparse four-piece bitmap input of the complete physically placed buffered core. -/
def bufferInput (g : GateTileState) : Bitmap.Input := (bufferAtlas g).input

end PushPuzzle.PushFS.Reduction.GateTileRouting

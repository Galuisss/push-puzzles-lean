/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Statics

/-! Exact shared-corner anchors, source-route tangents and complete literal seam guards. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

set_option maxHeartbeats 0
set_option maxRecDepth 65536

def inFlip : Kind→Bool
  | .inFlip | .both=>true
  | _=>false

def outFlip : Kind→Bool
  | .outFlip | .both=>true
  | _=>false

def cornerPoint (k : Kind) : Cell (width k) (height k) := (⟨10,by cases k <;> decide⟩,⟨10,by cases k <;> decide⟩)
def nearAnchor (k : Kind) : Cell (width k) (height k) := (⟨sourceX k,by cases k <;> decide⟩,⟨10,by cases k <;> decide⟩)
def farAnchor (k : Kind) : Cell (width k) (height k) := (⟨10,by cases k <;> decide⟩,⟨lastY k+2,by cases k <;> decide⟩)



end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners

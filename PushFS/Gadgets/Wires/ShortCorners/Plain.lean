/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Out

/-! The 29-box ordinary turn in the same corner and southern collar convention as the corrected short turns. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners.Plain

set_option maxRecDepth 65536
set_option maxHeartbeats 0
abbrev C := Cell 45 44
def hub : C := (38,21)
def corner (i : Fin 4) : C := ![(1,1),(43,1),(1,42),(43,42)] i

def wallTest (p : C) : Bool :=
  (if ht : 1≤p.2.val ∧p.2.val<42 then Turn.wallTest (p.1,⟨p.2.val-1,by omega⟩) else false) ||
    decide ((p.1.val=8 ∨p.1.val=9) ∧42≤p.2.val)

def reservedTest (p : C) : Bool :=
  if ht : 1≤p.2.val ∧p.2.val<42 then Turn.reservedTest (p.1,⟨p.2.val-1,by omega⟩) else false

def neighbors : Finset C := {(42,10),(44,10),(10,42)}

def place (p : Turn.C) : C := (p.1,⟨1+p.2.val,by have:=p.2.isLt; omega⟩)

def template : Template 45 44 29 where
  hub:=hub
  corner:=corner
  wall:=wallTest
  reserved p:=reservedTest p ||decide (p∈neighbors)
  neighbors:=neighbors
  zero i:=place (Turn.template.zero i)
  one i:=place (Turn.template.one i)
  forward:=Turn.forward
  backward:=Turn.backward
  walks i:=if i=0 then Turn.walk0++[.north] else if i=1 then Turn.walk1++[.north]
    else if i=2 then Turn.walk2++[.south,.south] else Turn.walk3++[.south,.south]

theorem checked : template.Checked where
  injective:=by decide +kernel
  slots_reserved:=by decide +kernel
  neighbors_reserved:=by decide +kernel
  neighbors_floor:=by decide +kernel
  static_paths:=by decide +kernel
  forward_checked:=by decide +kernel
  backward_checked:=by decide +kernel
  walks_checked:=by decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners.Plain

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.ShortCorners.Out
public import PushFS.Gadgets.Wires.ShortCorners.In

/-! The actual 47-box short turn with a real flip on both arms. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.ShortCorners.Both

set_option maxRecDepth 65536
set_option maxHeartbeats 0
abbrev C := Cell 63 64
def hub : C := (38,21)
def corner (i : Fin 4) : C := ![(1,1),(61,1),(1,62),(61,62)] i

def wallTest (p : C) : Bool :=
  (if ht : p.1.val<45 ∧p.2.val≥1 ∧p.2.val<42 then
      Turn.wallTest (⟨p.1.val,ht.1⟩,⟨p.2.val-1,by omega⟩) else false) ||
    (if hh : 38≤p.1.val ∧p.2.val<21 then
      Flip.wallTest (⟨62-p.1.val,by have:=p.1.isLt; omega⟩,⟨20-p.2.val,by omega⟩) else false) ||
    (if ho : p.1.val<21 ∧39≤p.2.val then
      Flip.wallTest (⟨p.2.val-39,by have:=p.2.isLt; omega⟩,⟨20-p.1.val,by omega⟩) else false)

def reservedTest (p : C) : Bool :=
  (if ht : p.1.val<45 ∧p.2.val≥1 ∧p.2.val<42 then
      Turn.reservedTest (⟨p.1.val,ht.1⟩,⟨p.2.val-1,by omega⟩) else false) ||
    (if hh : 38≤p.1.val ∧p.2.val<21 then
      Flip.reservedTest (⟨62-p.1.val,by have:=p.1.isLt; omega⟩,⟨20-p.2.val,by omega⟩) else false) ||
    (if ho : p.1.val<21 ∧39≤p.2.val then
      Flip.reservedTest (⟨p.2.val-39,by have:=p.2.isLt; omega⟩,⟨20-p.1.val,by omega⟩) else false)

def neighbors : Finset C := {(62,10),(10,62)}

def slots : List (C×C) :=
  [((60,10),(59,10)),
   ((58,10),(57,10)),
   ((56,10),(55,10)),
   ((54,10),(51,10)),
   ((50,10),(49,10)),
   ((48,10),(47,10)),
   ((46,10),(45,10)),
   ((44,10),(43,10)),
   ((42,10),(41,10)),
   ((40,10),(39,10)),
   ((38,10),(37,10)),
   ((36,10),(35,10)),
   ((34,10),(31,10)),
   ((30,10),(29,10)),
   ((28,10),(27,10)),
   ((26,10),(25,10)),
   ((24,10),(23,10)),
   ((22,10),(21,10)),
   ((20,10),(19,10)),
   ((18,10),(17,10)),
   ((16,10),(15,10)),
   ((14,10),(13,10)),
   ((12,10),(11,10)),
   ((10,11),(10,12)),
   ((10,13),(10,14)),
   ((10,15),(10,16)),
   ((10,17),(10,18)),
   ((10,19),(10,20)),
   ((10,21),(10,22)),
   ((10,23),(10,24)),
   ((10,25),(10,26)),
   ((10,27),(10,28)),
   ((10,29),(10,30)),
   ((10,31),(10,32)),
   ((10,33),(10,34)),
   ((10,35),(10,36)),
   ((10,37),(10,38)),
   ((10,39),(10,40)),
   ((10,41),(10,42)),
   ((10,43),(10,44)),
   ((10,45),(10,46)),
   ((10,47),(10,50)),
   ((10,51),(10,52)),
   ((10,53),(10,54)),
   ((10,55),(10,56)),
   ((10,57),(10,58)),
   ((10,59),(10,60))]

def toTailLow : List Direction := [.south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west]

def fromTailMixed : List Direction := [.north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east]

def toHeadMixed : List Direction := [.north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east]

def fromHeadHigh : List Direction := [.south, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west]

def toHeadHigh : List Direction := [.north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east]

def fromHeadMixed : List Direction := [.south, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west]

def toTailMixed : List Direction := [.south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west]

def fromTailLow : List Direction := [.north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east]

def forward : List Direction := toTailLow++Flip.forward.map Out.flipIso.directions++fromTailMixed++
  Turn.forward++toHeadMixed++Flip.forward.map In.flipIso.directions++fromHeadHigh

def backward : List Direction := toHeadHigh++Flip.backward.map In.flipIso.directions++fromHeadMixed++
  Turn.backward++toTailMixed++Flip.backward.map Out.flipIso.directions++fromTailLow

def walk0 : List Direction := [.north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .west, .west, .west, .north, .north, .north, .west, .north, .north, .north, .north, .north, .north, .north, .north, .north, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west]

def walk1 : List Direction := [.north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .north, .north, .north, .east, .north, .north, .north, .north, .north, .north, .north, .north, .north, .east, .east, .east, .east, .east, .east, .east, .east]

def walk2 : List Direction := [.south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .west, .north, .west, .west, .west, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .west, .west, .west, .west, .west, .west]

def walk3 : List Direction := [.east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .east, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south, .south]

def template : Template 63 64 47 where
  hub:=hub
  corner:=corner
  wall:=wallTest
  reserved p:=reservedTest p ||decide (p∈neighbors)
  neighbors:=neighbors
  zero i:=(slots.get i).1
  one i:=(slots.get i).2
  forward:=forward
  backward:=backward
  walks i:=if i=0 then walk0 else if i=1 then walk1 else if i=2 then walk2 else walk3

/-- Every actual box, permitted neighboring box and full real direction program is replayed in the kernel. -/
theorem checked : template.Checked where
  injective:=by decide +kernel
  slots_reserved:=by decide +kernel
  neighbors_reserved:=by decide +kernel
  neighbors_floor:=by decide +kernel
  static_paths:=by decide +kernel
  forward_checked:=by decide +kernel
  backward_checked:=by decide +kernel
  walks_checked:=by decide +kernel

end PushPuzzle.PushFS.Gadgets.Wires.ShortCorners.Both

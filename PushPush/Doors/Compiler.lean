/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.Layout
public import PushPush.Doors.CompilerLabels

/-! A regular chamber compiler for arbitrary directed self-closing door networks. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

/-- A door's six normal slots occupy one ninety-row chamber. -/
def doorBase (i : ℕ) : ℕ := 90 * i

/-- One slot per directed tunnel, and one slot for the initial signal. -/
def slots (I : Instance) : ℕ := 2 * I.doors.length + 1

/-- A uniform junction height leaves two protected rows at either endpoint. -/
def chamberHeight (I : Instance) : ℕ := 40 + 8 * slots I

/-- Each listed location receives a regular linear chain of binary choices. -/
def roomCount (I : Instance) : ℕ := (labels I).length * slots I

/-- Door chambers precede all location and choice chambers. -/
def roomBase (I : Instance) (v j : ℕ) : ℕ :=
  90 * I.doors.length + chamberHeight I * (slots I * v + j)

/-- All junction arrivals have private rows separated by eight cells. -/
def inputRow (I : Instance) (v j p : ℕ) : ℕ := roomBase I v j + 10 + 8 * p

/-- Upper exits lie against the upper endpoint cap. -/
def upperRow (I : Instance) (v j : ℕ) : ℕ := roomBase I v j + 3

/-- Lower exits lie against the lower endpoint cap. -/
def lowerRow (I : Instance) (v j : ℕ) : ℕ := roomBase I v j + chamberHeight I - 3

/-- Directed tunnel number `2*i+b`, in original door-list order. -/
def channelBit (j : ℕ) : Bool := decide (j % 2 = 1)

/-- Select the directed tunnel at the given dense channel index. -/
def channel (I : Instance) (j : ℕ) : SelfClosingDoor.Tunnel :=
  (I.doors.getD (j / 2) default).tunnel (channelBit j)

/-- A location's upper exit selects its current candidate directed tunnel. -/
def upperUsed (I : Instance) (v j : ℕ) : Bool :=
  if v = rank I I.target then decide (j = 0)
  else decide (j < 2 * I.doors.length ∧ rank I (channel I j).source = v)

/-- A lower exit skips one candidate, retaining the current source location. -/
def lowerUsed (I : Instance) (v j : ℕ) : Bool :=
  decide (v ≠ rank I I.target ∧ j < 2 * I.doors.length)

/-- The four internal return wires of each door chamber. -/
def internalWires (I : Instance) : List Wire :=
  (List.range I.doors.length).flatMap fun i =>
    let g := doorBase i
    [⟨g + 39, false, g + 80, true⟩, ⟨g + 79, false, g + 60, false⟩,
      ⟨g + 51, true, g + 10, false⟩, ⟨g + 11, true, g + 30, true⟩]

/-- Both successful door outputs enter their destination's root room. -/
def arrivalWire (I : Instance) (j : ℕ) : Wire :=
  ⟨doorBase (j / 2) + (if channelBit j then 29 else 61), !channelBit j,
    inputRow I (rank I (channel I j).target) 0 j, true⟩

/-- List the two outgoing channels of every door. -/
def arrivalWires (I : Instance) : List Wire :=
  (List.range (2 * I.doors.length)).map (arrivalWire I)

/-- At a matching candidate, the upper exit enters the corresponding check slot. -/
def choiceWires (I : Instance) : List Wire :=
  (List.range (labels I).length).flatMap fun v =>
    (List.range (2 * I.doors.length)).flatMap fun j =>
      if v ≠ rank I I.target ∧ rank I (channel I j).source = v then
        let one := channelBit j
        [⟨upperRow I v j, true, doorBase (j / 2) + (if one then 50 else 40), !one⟩]
      else []

/-- Skipping goes only to the next room of the same location's candidate chain. -/
def skipWires (I : Instance) : List Wire :=
  (List.range (labels I).length).flatMap fun v =>
    (List.range (2 * I.doors.length)).flatMap fun j =>
      if v ≠ rank I I.target then
        [⟨lowerRow I v j, false, inputRow I v (j + 1) 0, true⟩]
      else []

/-- The target's upper endpoint is the accepting signal parking place. -/
def targetRow (I : Instance) : ℕ := upperRow I (rank I I.target) 0

/-- Once at the original target, the storage cleanup visits the doors in list order. -/
def cleanupWires (I : Instance) : List Wire :=
  (List.range I.doors.length).map fun i =>
    ⟨if i = 0 then targetRow I else doorBase (i - 1) + 69,
      decide (i = 0), doorBase i + 70, true⟩

/-- Complete wire list, with cleanup present precisely for exact storage. -/
def wires (storage : Bool) (I : Instance) : List Wire :=
  internalWires I ++ arrivalWires I ++ choiceWires I ++ skipWires I ++
    if storage then cleanupWires I else []

/-- Initial physical row for each original door bit. -/
def dataRows (I : Instance) : List ℕ :=
  I.doors.zipIdx.map fun (e, i) => doorBase i + if e.initial then 60 else 30

/-- Regular chamber and wire layout for the original explicit door list. -/
def layout (storage : Bool) (I : Instance) : Layout where
  depth := 90 * I.doors.length + chamberHeight I * roomCount I
  rackRows :=
    (List.range I.doors.length).flatMap (fun i =>
      ([10, 30, 40, 50, 60, 80] ++ if storage then [70] else []).map (doorBase i + ·)) ++
    (List.range (roomCount I)).flatMap (fun j =>
      (List.range (slots I)).map fun p =>
        90 * I.doors.length + chamberHeight I * j + 10 + 8 * p)
  dividers := (List.range I.doors.length).map doorBase ++
    (List.range (roomCount I + 1)).map (fun j => 90 * I.doors.length + chamberHeight I * j)
  caps := (List.range (labels I).length).flatMap fun v =>
    (List.range (slots I)).flatMap fun j =>
      (if upperUsed I v j then [roomBase I v j + 2] else []) ++
        (if lowerUsed I v j then [roomBase I v j + chamberHeight I - 2] else [])
  dataRows := dataRows I
  goalRows := if storage then (List.range I.doors.length).map (fun i => doorBase i + 70)
    else dataRows I
  launch := inputRow I (rank I I.start) 0 (2 * I.doors.length)
  stop := if storage && decide (0 < I.doors.length) then doorBase (I.doors.length - 1) + 69
    else targetRow I
  wires := wires storage I

theorem slots_pos (I : Instance) : 0 < slots I := by unfold slots; omega

theorem chamberHeight_ge (I : Instance) : 48 ≤ chamberHeight I := by
  unfold chamberHeight slots
  omega

theorem dataRows_length (I : Instance) : (dataRows I).length = I.doors.length := by
  simp [dataRows]

theorem goalRows_length (storage : Bool) (I : Instance) :
    (layout storage I).goalRows.length = I.doors.length := by
  cases storage <;> simp [layout, dataRows_length]

theorem inputRow_interior (I : Instance) (v j p : ℕ) (hp : p < slots I) :
    roomBase I v j + 3 < inputRow I v j p ∧
      inputRow I v j p + 3 < roomBase I v j + chamberHeight I := by
  unfold inputRow chamberHeight
  omega

end PushPuzzle.PushPush.Doors.Source

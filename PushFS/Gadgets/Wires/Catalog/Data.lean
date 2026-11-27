/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushFS.Gadgets.Wires.Catalog.OutAtlas
public import PushFS.Gadgets.Wires.Catalog.InAtlas
public import PushFS.Gadgets.Wires.Catalog.Placed

/-! The seven actual physical logic-cell glyphs, with every source/goal owner, fixed endpoint chart and dense bitmap. -/

@[expose] public section
namespace PushPuzzle.PushFS.Gadgets.Wires.Catalog


open Reduction
set_option maxHeartbeats 1000000
set_option maxRecDepth 65536

inductive Kind
  | east | west | south | westSouth | eastSouth | southEast | southWest
  deriving DecidableEq

instance : Fintype Kind where
  elems:={.east,.west,.south,.westSouth,.eastSouth,.southEast,.southWest}
  complete k:=by cases k <;> simp

abbrev width : ℕ := 200005
abbrev height : ℕ := 198066
abbrev Cell := PushFS.Cell width height

def Labels : Kind→Type
  | .east | .west=>Chain.Label 200000
  | .south=>Chain.Label 198061
  | .westSouth=>Polyline.L.Label 99970 98999
  | .southWest=>Polyline.L.Label 99001 99969
  | .eastSouth=>(i : Fin 3)×Out.Labels 99970 98979 i
  | .southEast=>(i : Fin 3)×In.Labels 98981 99969 i

instance (k : Kind) : Fintype (Labels k) := by cases k <;> unfold Labels <;> infer_instance

def base (k : Kind) (a b : Bool) : Instance :=
  match k with
  | .east=>Chain.puzzle 200000 (by decide) a b
  | .west=>(Chain.puzzle 200000 (by decide) a b).reflectedX
  | .south=>(Chain.puzzle 198061 (by decide) a b).transposed.reflectedX
  | .westSouth=>(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle
  | .southWest=>((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle).reflectedX.transposed.reflectedX
  | .eastSouth=>((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle).reflectedX
  | .southEast=>((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).puzzle).reflectedX.transposed

def baseMatching (k : Kind) (a b : Bool) : SlotMatching (base k a b) (Labels k) :=
  match k with
  | .east=>Chain.slotMatching 200000 (by decide) a b
  | .west=>(Chain.slotMatching 200000 (by decide) a b).reorient (GridIsometry.reflectX 200005 21)
  | .south=>((Chain.slotMatching 198061 (by decide) a b).reorient (GridIsometry.transpose 198066 21)).reorient
      (GridIsometry.reflectX 21 198066)
  | .westSouth=>(Polyline.L.atlas 99970 98999 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching
  | .southWest=>((((Polyline.L.atlas 99001 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching).reorient
      (GridIsometry.reflectX 99044 100013)).reorient (GridIsometry.transpose 99044 100013)).reorient
      (GridIsometry.reflectX 100013 99044)
  | .eastSouth=>((Out.atlas 99970 98979 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching).reorient
      (GridIsometry.reflectX 100013 99043)
  | .southEast=>(((In.atlas 98981 99969 (by decide) (by decide) (Polyline.L.uniform a) (Polyline.L.uniform b)).slotMatching).reorient
      (GridIsometry.reflectX 99044 100013)).reorient (GridIsometry.transpose 99044 100013)

def dx : Kind→ℕ
  | .south | .westSouth | .southEast=>99992
  | _=>0

def dy : Kind→ℕ
  | .east | .west | .westSouth | .eastSouth=>99023
  | _=>0

theorem fitsX (k : Kind) (a b : Bool) : dx k+(base k a b).width≤width := by
  cases k
  · change 0+200005≤200005; decide
  · change 0+200005≤200005; decide
  · change 99992+21≤200005; decide
  · change 99992+100013≤200005; decide
  · change 0+100013≤200005; decide
  · change 99992+100013≤200005; decide
  · change 0+100013≤200005; decide

theorem fitsY (k : Kind) (a b : Bool) : dy k+(base k a b).height≤height := by
  cases k
  · change 99023+21≤198066; decide
  · change 99023+21≤198066; decide
  · change 0+198066≤198066; decide
  · change 99023+99043≤198066; decide
  · change 99023+99043≤198066; decide
  · change 0+99044≤198066; decide
  · change 0+99044≤198066; decide

/-- The complete physical logic-cell instance retains every real source and target owner. -/
def atlas (k : Kind) (a b : Bool) : StorageAtlas 1 width height (fun _=>Labels k) :=
  placedAtlas (baseMatching k a b) (dx k) (dy k) (fitsX k a b) (fitsY k a b)

def puzzle (k : Kind) (a b : Bool) : Instance := (atlas k a b).puzzle

def slotMatching (k : Kind) (a b : Bool) : SlotMatching (puzzle k a b) ((_i : Fin 1)×Labels k) :=
  (atlas k a b).slotMatching

def westPort : Cell := (2,99033)
def eastPort : Cell := (200002,99033)
def northPort : Cell := (100002,2)
def southPort : Cell := (100002,198063)

def sourcePort : Kind→Cell
  | .east | .eastSouth=>westPort
  | .west | .westSouth=>eastPort
  | .south | .southEast | .southWest=>northPort

def targetPort : Kind→Cell
  | .east | .southEast=>eastPort
  | .west | .southWest=>westPort
  | .south | .westSouth | .eastSouth=>southPort

def sourceDirection : Kind→Direction
  | .east | .eastSouth=>.east
  | .west | .westSouth=>.west
  | .south | .southEast | .southWest=>.south

def targetDirection : Kind→Direction
  | .east | .southEast=>.east
  | .west | .southWest=>.west
  | .south | .westSouth | .eastSouth=>.south

end PushPuzzle.PushFS.Gadgets.Wires.Catalog

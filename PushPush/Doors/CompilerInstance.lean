/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.CompilerBalance
public import PushPush.Doors.CompilerPolyTime

/-! Genuine wall-free puzzle instances of the explicit self-closing-door compiler. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity Turing.MultiTapeTM

/-- The real unlabelled work board, with all static pins, rack boxes and door bits. -/
def puzzle (storage : Bool) (I : Instance) : PushS.Instance :=
  (layout storage I).toStorage (layout_balanced storage I).card_eq

/-- The compiler writes exactly the explicit dense physical rectangle. -/
@[fun_prop] theorem puzzle_polyTime (storage : Bool) :
    ComputableInPolyTime (puzzle storage) SelfClosingDoor.encInstance PushS.encoding :=
  Layout.toStorage_polyTime (layout_polyTime storage) (fun I => (layout_balanced storage I).card_eq)

@[simp] theorem puzzle_width (storage : Bool) (I : Instance) :
    (puzzle storage I).width = (layout storage I).width := rfl

@[simp] theorem puzzle_height (storage : Bool) (I : Instance) :
    (puzzle storage I).height = (layout storage I).height := rfl

@[simp] theorem puzzle_initial (storage : Bool) (I : Instance) :
    (puzzle storage I).initial = (layout storage I).initial := rfl

@[simp] theorem puzzle_boxes (storage : Bool) (I : Instance) :
    (puzzle storage I).initial.boxes = (layout storage I).raster (layout storage I).initialRaw := rfl

@[simp] theorem puzzle_goals (storage : Bool) (I : Instance) :
    (puzzle storage I).board.goals = (layout storage I).raster (layout storage I).goalsRaw := rfl

@[simp] theorem puzzle_player (storage : Bool) (I : Instance) :
    (puzzle storage I).initial.player = (layout storage I).corner := rfl

end PushPuzzle.PushPush.Doors.Source

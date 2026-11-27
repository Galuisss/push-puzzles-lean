/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.Doors.ColumnSoundness
public import PushPush.Doors.RestoredFrame
public import PushPush.Doors.QuotasForward

/-! The source-side acceptance certificate extracted by the seven-round whole-run reader. -/

@[expose] public section
namespace PushPuzzle.PushPush.Doors.Source

open Cslib.Complexity

structure ReaderTerminal (I : Instance)
    (final : PushFS.State (layout false I).width (layout false I).height) : Prop where
  frame : RestoredFrame false I final
  columns : PrivateColumnInventory false I final.boxes
  parked : workCell false I (targetRow I) (targetRow_fit false I) ∈ final.boxes

theorem ReaderTerminal.sound {I : Instance}
    {final : PushFS.State (layout false I).width (layout false I).height}
    (H : ReaderTerminal I final) (hactual : Reachable (readerSource I).initial final) :
    I ∈ SelfClosingDoor.Reachability := by
  apply physical_columns_sound false I H.frame.corridor H.columns ?_ hactual H.parked
  change (puzzle false I).initial.boxes = (Stock.initial false I).boxes false
  exact (congrArg PushFS.State.boxes (Stock.initial_canonical false I)).symm

end PushPuzzle.PushPush.Doors.Source

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicErase
public import Push.CyclicPolyTime

/-! Standard polynomial-time emission of the actual wider reader, dock, and turned erase source. -/

public section
namespace PushPuzzle.Push.CyclicErase

open Turing.MultiTapeTM
open scoped PushPuzzle.Push.ColumnScan

/-- Write the source-width extra room reserve directly into the ordinary unary source recipe. -/
@[fun_prop] theorem asReader_polyTime : ComputableInPolyTime asReader
    ColumnScan.Input.encoding ColumnScan.Input.encoding := by
  have hw : ComputableInPolyTime ColumnScan.Input.width ColumnScan.Input.encoding encUnary :=
    ColumnScan.encData_width_polyTime ColumnScan.Input.data_polyTime
  have h : ComputableInPolyTime
      (fun r : ColumnScan.Input => { ColumnScan.Input.data r with extraWidth := r.width })
      ColumnScan.Input.encoding ColumnScan.encData := by fun_prop
  exact h.of_enc_eq fun _ => rfl

/-- Emit the complete actual reader with `2w+2` room columns in standard polynomial time. -/
@[fun_prop] theorem wideEraseReader_polyTime : ComputableInPolyTime wideEraseReader
    ColumnScan.Input.encoding ColumnScan.Input.encoding :=
  Cyclic.wideReader_polyTime.comp asReader_polyTime

/-- Emit the actual southwest dock, retaining its complete dense source bitmap. -/
@[fun_prop] theorem eraseDock_polyTime : ComputableInPolyTime eraseDock
    ColumnScan.Input.encoding CornerDock.Input.encoding :=
  Cyclic.dock_polyTime.comp asReader_polyTime

/-- The actual next live source is the physical quarter turn of the wider erase dock. -/
@[fun_prop] theorem nextSource_polyTime : ComputableInPolyTime
    (fun r : ColumnScan.Input => Cyclic.turn (eraseDock r).compile)
    ColumnScan.Input.encoding Push.encoding :=
  Cyclic.nextSource_polyTime.comp asReader_polyTime

end PushPuzzle.Push.CyclicErase

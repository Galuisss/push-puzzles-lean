/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScan
public import Push.SealedDoor

/-! Filling the column reader's unique source door is irreversible. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : ColumnScan.Input)

/-- The permanent northeast solid region prevents every way of reopening a filled source door. -/
private theorem move_door_full {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Reachable r.compile.board none r.compile.initial s)
    (hm : Move r.compile.board none d s t) (hs : r.door ∈ s.boxes) : r.door ∈ t.boxes := by
  apply SealedDoor.move_full r.door rfl _ (r.east_full hr) (r.northeast_full hr) hm hs
  change r.height - 1 + 1 = r.height
  have := r.height_pos
  omega

private theorem step_door_full {s t : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.compile.initial s)
    (hm : Step r.compile.board none s t) (hs : r.door ∈ s.boxes) : r.door ∈ t.boxes :=
  r.move_door_full hr hm.choose_spec hs

/-- Once the commit seal fills the source door, every later prefix keeps it filled. -/
theorem reachable_door_full {s t : State r.outputWidth r.outputHeight}
    (hs : Reachable r.compile.board none r.compile.initial s)
    (hr : Reachable r.compile.board none s t) (hdoor : r.door ∈ s.boxes) : r.door ∈ t.boxes := by
  induction hr with
  | refl => exact hdoor
  | tail hsu hm ih => exact r.step_door_full (hs.trans hsu) hm ih

end PushPuzzle.Push.ColumnScan.Input

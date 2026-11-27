/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.ColumnScanForwardExact
public import Push.CornerDockBackup

/-! A widened actual reader and backup rows already present in its southwest dock. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

/-- Use the ordinary cyclic soundness layer with an additional source-width room reserve. -/
abbrev asReader (r : ColumnScan.Input) : ColumnScan.Input :=
  { r with extraWidth := r.width }

/-- Each auxiliary row has room for `w` backup moves and `w+2` later cleanup reads. -/
abbrev wideEraseReader (r : ColumnScan.Input) : ColumnScan.Input :=
  Cyclic.wideReader (asReader r)

/-- Attach the literal southwest dock to the reader with its wider room. -/
abbrev eraseDock (r : ColumnScan.Input) : CornerDock.Input := Cyclic.dock (asReader r)

theorem backup_row_lt (r : ColumnScan.Input) (hk : r.height ≤ r.quota) (i : Fin r.height) :
    (wideEraseReader r).targetLevel + i.val < (wideEraseReader r).outputHeight := by
  have hs := (wideEraseReader r).separation
  have hh := r.height_pos
  have hi := i.isLt
  change r.quota + max r.sourceHoles r.width + 4 ≤ (wideEraseReader r).length at hs
  change (wideEraseReader r).firstLevel - r.quota + i.val < r.height + (wideEraseReader r).length
  change r.height - 1 + (wideEraseReader r).length - 2 - r.quota + i.val <
    r.height + (wideEraseReader r).length
  omega

/-- One of the actual old auxiliary rows, starting at the first reader's left target row. -/
@[expose] def backupRow (r : ColumnScan.Input) (hk : r.height ≤ r.quota) (i : Fin r.height) :
    Fin (eraseDock r).outputHeight :=
  ⟨(wideEraseReader r).targetLevel + i.val, (backup_row_lt r hk i).trans_le (by
    change (wideEraseReader r).outputHeight ≤ (wideEraseReader r).outputHeight + (eraseDock r).distance
    omega)⟩

/-- The literal list of all `h` backup rows, in increasing order. -/
@[expose] def backupRows (r : ColumnScan.Input) (hk : r.height ≤ r.quota) :
    List (Fin (eraseDock r).outputHeight) := List.ofFn (backupRow r hk)

theorem backupRows_nodup (r : ColumnScan.Input) (hk : r.height ≤ r.quota) : (backupRows r hk).Nodup := by
  rw [backupRows, List.nodup_ofFn]
  intro i j he
  have h := congrArg Fin.val he
  apply Fin.ext
  change (wideEraseReader r).targetLevel + i.val = (wideEraseReader r).targetLevel + j.val at h
  omega

theorem backupRows_bounds (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (row : Fin (eraseDock r).outputHeight) (hr : row ∈ backupRows r hk) :
    (wideEraseReader r).targetLevel ≤ row.val ∧ row.val < (wideEraseReader r).outputHeight := by
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hr
  exact ⟨Nat.le_add_right _ _, backup_row_lt r hk i⟩

theorem backupRows_source_below (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (row : Fin (eraseDock r).outputHeight) (hr : row ∈ backupRows r hk) : r.height ≤ row.val := by
  have hl := (wideEraseReader r).targetLevel_lower
  have hh := (backupRows_bounds r hk row hr).1
  change r.height + max r.sourceHoles r.width < (wideEraseReader r).targetLevel at hl
  omega

end PushPuzzle.Push.CyclicErase

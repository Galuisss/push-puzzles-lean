/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseInventory
public import Push.CyclicErasePeelingSoundness
public import Push.CyclicTurnProgram

/-! The literal erase replacement program satisfies the next source's actual hole budget. -/

public section
namespace PushPuzzle.Push.Scan

open PushFS

/-- Concatenating static programs adds exactly their positive read quotas. -/
theorem quota_append {w h : ℕ} (a b : List (Instruction w h)) : quota (a ++ b) = quota a + quota b := by
  simp only [quota, List.map_append, List.sum_append]

/-- Each parallel request contributes exactly its own literal quota. -/
theorem lines_quota {w h : ℕ} (side : Direction) (requests : List (ℕ × ℕ)) :
    quota (lines (w := w) (h := h) side requests) = (requests.map Prod.snd).sum := by
  simp only [quota, lines, List.map_map, Function.comp_def, Instruction.quota]

/-- Enumerating a dense quota vector retains its complete positive budget. -/
theorem dense_lines_quota {w h : ℕ} (side : Direction) (quotas : List ℕ) :
    quota (lines (w := w) (h := h) side (ofQuotas quotas)) = quotas.sum := by
  rw [lines_quota]
  simp only [ofQuotas, List.map_ofFn, Function.comp_def]
  congr 1
  exact List.ofFn_getElem

end PushPuzzle.Push.Scan
namespace PushPuzzle.Push.Cyclic

open PushFS

/-- Source embedding changes only lane coordinates and preserves every positive read quota. -/
theorem sourceProgram_quota (r : ColumnScan.Input) (program : List (Scan.Instruction r.width r.height)) :
    Scan.quota (program.map (sourceInstruction r)) = Scan.quota program := by
  induction program with
  | nil => rfl
  | cons i program ih =>
    simp only [List.map_cons, Scan.quota, List.map_cons, List.sum_cons] at ih ⊢
    have hi : (sourceInstruction r i).quota = i.quota := by cases i <;> rfl
    rw [hi, ih]

end PushPuzzle.Push.Cyclic
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS

private theorem selectedColumns_length (r : ColumnScan.Input) (selected : Finset (Fin r.width)) :
    (selectedColumns r selected).length = selected.card := by
  have hnd : (selectedColumns r selected).Nodup := (List.nodup_finRange r.width).filter _
  have he : (selectedColumns r selected).toFinset = selected := by
    ext x
    simp [selectedColumns]
  have hc := List.toFinset_card_of_nodup hnd
  rw [he] at hc
  exact hc.symm

/-- One height quota is charged for each distinct selected original source column. -/
private theorem eraseProgram_quota (r : ColumnScan.Input) (selected : Finset (Fin r.width)) :
    Scan.quota (eraseProgram r selected) = r.height * selected.card := by
  rw [eraseProgram, Scan.lines_quota]
  simp only [eraseRequests, List.map_map, Function.comp_def]
  rw [List.map_const', List.sum_replicate, selectedColumns_length]
  exact Nat.mul_comm _ _

private theorem cleanup_quota (r : ColumnScan.Input) :
    Scan.quota (Cyclic.rowProgram (w := (eraseDock r).outputWidth) (h := (eraseDock r).outputHeight)
      (Cyclic.auxiliaryRows r) (r.width + 2)) =
        (r.width + 2) * ((wideEraseReader r).outputHeight - r.height) := by
  simp only [Cyclic.rowProgram, Scan.quota, List.map_map, Function.comp_def, Scan.Instruction.quota]
  rw [List.map_const', List.sum_replicate]
  simp only [Cyclic.auxiliaryRows, List.length_map, List.length_range]
  exact Nat.mul_comm _ _

/-- Exact positive quota of the literal original-row / north-erase / auxiliary-cleanup / future-tail replacement. -/
private theorem unturnedProgram_quota (r : ColumnScan.Input) (rows : List ℕ) (selected : Finset
    (Fin r.width))
    (tail : List (Scan.Instruction r.width r.height)) :
    Scan.quota (unturnedProgram r rows selected tail) = rows.sum + r.height * selected.card +
      (r.width + 2) * ((wideEraseReader r).outputHeight - r.height) + Scan.quota tail := by
  simp only [unturnedProgram, Scan.quota_append, Cyclic.sourceProgram_quota,
    Scan.dense_lines_quota, eraseProgram_quota, cleanup_quota]

/-- The actual unturned erase replacement lies in the next dense reader's quota domain. -/
private theorem unturnedProgram_budget (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (rows : List ℕ) (selected : Finset (Fin r.width)) (tail : List (Scan.Instruction r.width r.height))
    (hfuture : rows.sum + Scan.quota tail ≤ r.sourceHoles) :
    Scan.quota (unturnedProgram r rows selected tail) ≤
      (holes (Cyclic.turn (eraseDock r).compile).initial).card := by
  rw [unturnedProgram_quota]
  have h := erase_read_budget r hk selected (rows.sum + Scan.quota tail) hfuture
  omega

/-- Turning the complete actual replacement retains the same certified quota budget. -/
theorem turnedProgram_budget (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (rows : List ℕ) (selected : Finset (Fin r.width)) (tail : List (Scan.Instruction r.width r.height))
    (hfuture : rows.sum + Scan.quota tail ≤ r.sourceHoles) :
    Scan.quota (Cyclic.turnProgram (unturnedProgram r rows selected tail)) ≤
      (holes (Cyclic.turn (eraseDock r).compile).initial).card := by
  rw [Cyclic.turnProgram_quota]
  exact unturnedProgram_budget r hk rows selected tail hfuture

end PushPuzzle.Push.CyclicErase

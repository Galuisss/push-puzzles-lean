/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicPeeling
public import Push.ScanVectors

/-! The peeled continuation starts with the actual dense next-reader quota vector. -/

@[expose] public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Future source instructions translated into the actual next source's coordinates. -/
def nextTail (r : ColumnScan.Input) (tail : List (Scan.Instruction r.width r.height)) :
    List (Scan.Instruction (dock r).outputHeight (dock r).outputWidth) :=
  turnProgram (tail.map (sourceInstruction r))

private theorem turn_source_rows (r : ColumnScan.Input) (rows : List ℕ) :
    turnProgram ((Scan.lines .west (Scan.ofQuotas rows)).map (sourceInstruction r)) =
      Scan.columns (Scan.ofQuotas rows) := by
  simp only [turnProgram, Scan.columns, Scan.lines, List.map_map]
  rfl

private theorem turn_cleanup (r : ColumnScan.Input) :
    turnProgram (w := (dock r).outputWidth) (h := (dock r).outputHeight)
      (rowProgram (auxiliaryRows r) (r.width + 2)) =
      Scan.columns (((List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2)).mapIdx
        (fun lane quota => (r.height + lane, quota)))) := by
  simp only [turnProgram, rowProgram, auxiliaryRows, List.map_map,
    List.mapIdx_replicate, Scan.columns, Scan.lines]
  rfl

/-- Literal peeling is the next dense column block followed by the transformed future source program. -/
theorem peeledProgram_eval (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (E : Finset (Cell (dock r).outputHeight (dock r).outputWidth)) :
    Scan.eval (peeledProgram r rows tail) E =
      Scan.eval (Scan.columns (Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail) E := by
  have hp : peeledProgram r rows tail =
      Scan.columns (Scan.ofQuotas rows) ++
      Scan.columns ((List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2)).mapIdx
        (fun lane quota => (r.height + lane, quota))) ++ nextTail r tail := by
    change (List.map (turnInstruction (w := (dock r).outputWidth) (h := (dock r).outputHeight))
      (((Scan.lines .west (Scan.ofQuotas rows)).map (sourceInstruction r) ++
        rowProgram (auxiliaryRows r) (r.width + 2)) ++ tail.map (sourceInstruction r))) = _
    rw [List.map_append, List.map_append]
    change turnProgram _ ++ turnProgram _ ++ nextTail r tail = _
    rw [turn_source_rows, turn_cleanup]
  have hc : Scan.columns (w := (dock r).outputHeight) (h := (dock r).outputWidth) (Scan.ofQuotas (rows ++
      List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2))) =
      Scan.columns (Scan.ofQuotas rows) ++
        Scan.columns ((List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2)).mapIdx
          (fun lane quota => (r.height + lane, quota))) := by
    rw [Scan.ofQuotas_append, hlen]
    simp only [Scan.columns, Scan.lines, List.map_append]
  rw [hp]
  simp only [Scan.eval_append]
  change _ = (Scan.eval (Scan.columns (Scan.ofQuotas ((rows ++
    List.replicate ((wideReader r).outputHeight - r.height) (r.width + 2)) ++
    List.replicate ((dock r).outputHeight - (wideReader r).outputHeight) 0))) E).bind _
  rw [Scan.eval_columns_zero_pad, hc, Scan.eval_append]

end PushPuzzle.Push.Cyclic

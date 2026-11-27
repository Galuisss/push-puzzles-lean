/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRoundBudget
public import Push.CyclicErasePeelingCorrectness
public import Push.CyclicSchedulePeeling
import all Push.CyclicPeelingProgram

/-! The literal six-read replacement of one compact source-column clear. -/

@[expose] public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS AcceptanceProgram

/-- Finite actual source columns named by a bounded family of raw lane numbers. -/
def selectColumns (r : ColumnScan.Input) (lanes : Finset ℕ) : Finset (Fin r.width) :=
  Finset.univ.filter fun x => x.val ∈ lanes

theorem clearColumns_select (r : ColumnScan.Input) (lanes : Finset ℕ)
    (hb : ∀ lane ∈ lanes, lane < r.width) : clearColumns (selectColumns r lanes) = lanes := by
  ext lane
  simp only [clearColumns, selectColumns, Finset.mem_image, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact hx
  · intro hl
    exact ⟨⟨lane, hb lane hl⟩, hl, rfl⟩

/-- Actual selected finite columns enumerate the same increasing raw lane set. -/
private theorem selectedColumns_select (r : ColumnScan.Input) (lanes : Finset ℕ)
    (hb : ∀ lane ∈ lanes, lane < r.width) :
    (selectedColumns r (selectColumns r lanes)).map Fin.val = lanes.sort (· ≤ ·) := by
  let xs := (selectedColumns r (selectColumns r lanes)).map Fin.val
  have hn : xs.Nodup := List.Nodup.map Fin.val_injective ((List.nodup_finRange r.width).filter _)
  have ho : xs.Pairwise (· ≤ ·) := by
    rw [List.pairwise_map]
    exact (List.pairwise_le_finRange r.width).filter _
  have he : xs.toFinset = lanes := by
    ext lane
    simp only [xs, selectedColumns, selectColumns, List.mem_toFinset, List.mem_map,
      List.mem_filter, List.mem_finRange, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hl
      exact ⟨⟨lane, hb lane hl⟩, hl, rfl⟩
  exact ((List.toFinset_sort (· ≤ ·) hn).mpr ho).symm.trans (congrArg (fun s => s.sort (· ≤ ·)) he)

/-- The actual north erase requests emit directly from the canonical raw clear-lane list. -/
theorem eraseRequests_select (r : ColumnScan.Input) (lanes : Finset ℕ)
    (hb : ∀ lane ∈ lanes, lane < r.width) :
    eraseRequests r (selectColumns r lanes) =
      (lanes.sort (· ≤ ·)).map (fun lane => (lane + 2, r.height)) := by
  have he := congrArg (List.map (fun lane => (lane + 2, r.height))) (selectedColumns_select r lanes hb)
  simpa only [eraseRequests, List.map_map, Function.comp_def] using he

/-- The new first south read charges only original source rows. -/
def firstQuotas (r : ColumnScan.Input) (rows : List ℕ) : List ℕ :=
  rows ++ List.replicate ((nextSource r).width - r.height) 0

theorem firstQuotas_length (r : ColumnScan.Input) (rows : List ℕ) (hlen : rows.length = r.height) :
    (firstQuotas r rows).length = (nextSource r).width := by
  have hh : r.height ≤ (nextSource r).width := by
    change r.height ≤ r.height + r.length + (eraseDock r).distance
    omega
  simp only [firstQuotas, List.length_append, List.length_replicate, hlen]
  omega

theorem firstQuotas_sum (r : ColumnScan.Input) (rows : List ℕ) :
    (firstQuotas r rows).sum = rows.sum := by
  simp only [firstQuotas, List.sum_append, List.sum_replicate, smul_eq_mul, Nat.mul_zero, Nat.add_zero]

/-- The five remaining read blocks after the new first south read. -/
def suffixRounds (r : ColumnScan.Input) (selected : Finset (Fin r.width)) (tail : List Round) : List Round :=
  [.read .west (Cyclic.turnRequests (eraseDock r).outputWidth .north (eraseRequests r selected)),
    .read .north [], .read .east [],
    .read .south ((Cyclic.auxiliaryRows r).map fun lane => (lane, r.width + 2)), .read .west []] ++
    Cyclic.nextRounds (asReader r) tail

/-- The actual compact replacement has exactly the fixed erase-peeling skeleton. -/
theorem suffixRounds_shapes (r : ColumnScan.Input) (selected : Finset (Fin r.width)) (tail : List Round) :
    (suffixRounds r selected tail).map Round.shape = CyclicSchedule.eraseSuffix (tail.map Round.shape) := by
  simp only [suffixRounds, List.map_append, List.map_cons, List.map_nil, Round.shape,
    Cyclic.nextRounds_shapes, CyclicSchedule.eraseSuffix, CyclicSchedule.turnShapes]

private theorem transformed_instructions (r : ColumnScan.Input) (rows : List ℕ)
    (selected : Finset (Fin r.width)) (tail : List Round) :
    peeledProgram r rows selected (instructions tail) =
      Scan.columns (Scan.ofQuotas rows) ++
        instructions (w := (eraseDock r).outputHeight) (h := (eraseDock r).outputWidth)
          (suffixRounds r selected tail) := by
  have he : peeledProgram r rows selected (instructions tail) =
      Scan.columns (Scan.ofQuotas rows) ++
        Scan.lines .west (Cyclic.turnRequests (eraseDock r).outputWidth .north (eraseRequests r selected)) ++
        Scan.lines .south ((Cyclic.auxiliaryRows r).map fun lane => (lane, r.width + 2)) ++
        Cyclic.nextTail (asReader r) (instructions tail) := by
    simp only [peeledProgram, unturnedProgram, Cyclic.turnProgram, List.map_append,
      Scan.columns, Scan.lines, eraseProgram, Cyclic.turnRequests, Cyclic.rowProgram,
      Cyclic.nextTail, List.map_map]
    rfl
  have hs : instructions (w := (eraseDock r).outputHeight) (h := (eraseDock r).outputWidth)
      (suffixRounds r selected tail) =
        Scan.lines .west (Cyclic.turnRequests (eraseDock r).outputWidth .north (eraseRequests r selected)) ++
        (Scan.lines .south ((Cyclic.auxiliaryRows r).map fun lane => (lane, r.width + 2)) ++
          Cyclic.nextTail (asReader r) (instructions tail)) := by
    change (Scan.lines .west (Cyclic.turnRequests (eraseDock r).outputWidth .north (eraseRequests r selected)) ++
      (Scan.lines .south ((Cyclic.auxiliaryRows r).map fun lane => (lane, r.width + 2)) ++
        instructions (Cyclic.nextRounds (asReader r) tail))) = _
    rw [Cyclic.nextRounds_instructions]
  rw [he, hs]
  simp only [List.append_assoc]

/-- The padded first vector and all six literal read rounds execute exactly the physical erase replacement. -/
private theorem suffixRounds_eval (r : ColumnScan.Input) (rows : List ℕ)
    (selected : Finset (Fin r.width)) (tail : List Round)
    (E : Finset (Cell (eraseDock r).outputHeight (eraseDock r).outputWidth)) :
    Scan.eval (Scan.columns (Scan.ofQuotas (firstQuotas r rows)) ++
      instructions (suffixRounds r selected tail)) E =
    Scan.eval (peeledProgram r rows selected (instructions tail)) E := by
  rw [transformed_instructions, Scan.eval_append, Scan.eval_append, firstQuotas,
    Scan.eval_columns_zero_pad]

/-- Acceptance is unchanged by the literal compact six-read replacement. -/
theorem suffixRounds_accepts_iff (r : ColumnScan.Input) (rows : List ℕ)
    (selected : Finset (Fin r.width)) (tail : List Round)
    (E : Finset (Cell (eraseDock r).outputHeight (eraseDock r).outputWidth)) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas (firstQuotas r rows)) ++
      instructions (suffixRounds r selected tail)) E ↔
      Scan.Accepts (peeledProgram r rows selected (instructions tail)) E := by
  simp only [Scan.Accepts, suffixRounds_eval]

/-- The padded first read plus all compact replacement blocks retain the exact physical quota. -/
theorem suffixRounds_quota (r : ColumnScan.Input) (rows : List ℕ)
    (selected : Finset (Fin r.width)) (tail : List Round) :
    (firstQuotas r rows).sum + Scan.quota
      (instructions (w := (eraseDock r).outputHeight) (h := (eraseDock r).outputWidth)
        (suffixRounds r selected tail)) =
      Scan.quota (peeledProgram r rows selected (instructions tail)) := by
  rw [transformed_instructions, Scan.quota_append, Scan.columns, Scan.dense_lines_quota, firstQuotas_sum]

end PushPuzzle.Push.CyclicErase

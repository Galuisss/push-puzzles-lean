/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Slots
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Polynomial-time actual within-panel slots

The actual placement orders each row's original indices increasingly. Its slot is computed by
counting earlier original indices with the same row value. This list scan uses the standard
unary row-array/index encoding and agrees with the existing finite-set placement algorithm.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.slot`: explicit earlier-index row count.
* `PushPuzzle.NCL.Strip.PolyTime.address`: actual flattened panel/slot address.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.computableInPolyTime_slot`: standard encoded polynomial-time slot scan.
* `PushPuzzle.NCL.Strip.PolyTime.ofRows_slot`: exact agreement with the actual existing placement.
* `PushPuzzle.NCL.Strip.PolyTime.ofRows_address`: exact flattened-address agreement.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

/-- Count original earlier indices carrying the same row as the selected original index. -/
@[expose] def slot (rows : List ℕ) (index : ℕ) : ℕ :=
  ((List.range rows.length).filter
    (fun j => decide (j < index ∧ rows.getD j 0 = rows.getD index 0))).length

/-- The actual row-array slot scan is polynomial-time under standard explicit unary codes. -/
theorem computableInPolyTime_slot :
    ComputableInPolyTime (fun p : List ℕ × ℕ => slot p.1 p.2)
      (encPair (encList encUnary) encUnary) encUnary := by
  unfold slot
  have hf : ComputableInPolyTime (fun p : List ℕ × ℕ =>
      (List.range p.1.length).filter
        (fun j => decide (j < p.2 ∧ p.1.getD j 0 = p.1.getD p.2 0)))
      (encPair (encList encUnary) encUnary) (encList encUnary) := by
    apply ComputableInPolyTime.filterWithInput
    · fun_prop
    · fun_prop
  fun_prop

/-- Flatten the selected source row and its actual earlier-index slot. -/
@[expose] def address (capacity : ℕ) (rows : List ℕ) (index : ℕ) : ℕ :=
  capacity * rows.getD index 0 + slot rows index

/-- Standard encoded computation of the actual flattened panel/slot address. -/
theorem computableInPolyTime_address (capacity : ℕ) :
    ComputableInPolyTime (fun p : List ℕ × ℕ => address capacity p.1 p.2)
      (encPair (encList encUnary) encUnary) encUnary := by
  have hs := computableInPolyTime_slot
  unfold address
  fun_prop

private theorem rowIndices_eq {n : ℕ} (rows : Fin n → ℕ) (row : ℕ) :
    PushPuzzle.NCL.Strip.Placement.rowIndices rows row =
      (List.finRange n).filter (fun i => decide (rows i = row)) := by
  let xs := (List.finRange n).filter (fun i => decide (rows i = row))
  have hn : xs.Nodup := (List.nodup_finRange n).filter _
  have hs : xs.Pairwise (· ≤ ·) := (List.pairwise_le_finRange n).filter _
  have he : xs.toFinset = Finset.univ.filter (fun i => rows i = row) := by
    ext i
    simp [xs]
  unfold PushPuzzle.NCL.Strip.Placement.rowIndices
  rw [← he]
  exact (List.toFinset_sort (fun i j : Fin n => i ≤ j) hn).mpr hs

private theorem idxOf_eq_filter_lt {α : Type*} [LinearOrder α] (xs : List α)
    (hs : xs.Pairwise (· < ·)) (a : α) (ha : a ∈ xs) :
    xs.idxOf a = (xs.filter (fun x => decide (x < a))).length := by
  induction xs with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b xs ih =>
    rcases List.mem_cons.mp ha with hab | ha
    · subst a
      have he : xs.filter (fun x => decide (x < b)) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro x hx
        simpa only [decide_eq_true_eq, not_lt] using (List.rel_of_pairwise_cons hs hx).le
      simp [he]
    · have hba := List.rel_of_pairwise_cons hs ha
      simpa [List.idxOf_cons, ne_of_lt hba, hba] using ih hs.of_cons ha

/-- The list scan computes the exact original slot assigned by the actual finite placement. -/
theorem ofRows_slot {n capacity : ℕ} (rows : Fin n → ℕ)
    (bound : ∀ row, Fintype.card {i // rows i = row} ≤ capacity) (i : Fin n) :
    ((PushPuzzle.NCL.Strip.Placement.ofRows rows bound).slot i).val = slot (List.ofFn rows) i.val := by
  have hget (j : Fin n) : (List.ofFn rows).getD j.val 0 = rows j := by
    simp [List.getD_eq_getElem?_getD, j.isLt]
  have hfin : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem
    · simp
    intro j hj hk
    simp
  have hm : ((List.finRange n).filter
      (fun j => decide (j < i ∧ rows j = rows i))).map Fin.val =
      (List.range n).filter (fun j => decide
        (j < i.val ∧ (List.ofFn rows).getD j 0 = (List.ofFn rows).getD i.val 0)) := by
    rw [← hfin, List.filter_map]
    apply congrArg (List.map Fin.val)
    apply List.filter_congr
    intro j _
    simp only [Function.comp_def, hget j, hget i, Fin.lt_def]
  change (PushPuzzle.NCL.Strip.Placement.rowIndices rows (rows i)).idxOf i = _
  have hs : (PushPuzzle.NCL.Strip.Placement.rowIndices rows (rows i)).Pairwise (· < ·) :=
    (Finset.sortedLT_sort _).pairwise
  rw [idxOf_eq_filter_lt _ hs i (by simp [PushPuzzle.NCL.Strip.Placement.rowIndices])]
  rw [rowIndices_eq, List.filter_filter]
  simp only [← Bool.decide_and]
  have hlen := congrArg List.length hm
  simpa only [List.length_map, slot, List.length_ofFn] using hlen

/-- The standard list computation retains the exact original flattened panel/slot address. -/
theorem ofRows_address {n capacity : ℕ} (rows : Fin n → ℕ)
    (bound : ∀ row, Fintype.card {i // rows i = row} ≤ capacity) (i : Fin n) :
    (PushPuzzle.NCL.Strip.Placement.ofRows rows bound).address i = address capacity (List.ofFn rows) i.val := by
  have hget : (List.ofFn rows).getD i.val 0 = rows i := by
    simp [List.getD_eq_getElem?_getD, i.isLt]
  simp only [PushPuzzle.NCL.Strip.Placement.address, PushPuzzle.NCL.Strip.Placement.ofRows_row, address, ofRows_slot, hget]

end PushPuzzle.NCL.Strip.PolyTime

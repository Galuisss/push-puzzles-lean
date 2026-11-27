/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholeColumns
public import PushPush.ReadExact

/-! Extract each physical whole-column read and its paid quota from a loose scan. -/

@[expose] public section
namespace PushPuzzle.PushPush.WholeScan

open PushFS (Cell)
open Push.ReaderResidual Reader

variable {w h : ℕ}

private theorem LooseExec.columns_remainder {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : LooseExec (Push.Scan.columns requests) E F) : BottomRemainder E F := by
  induction requests generalizing E with
  | nil => cases H; exact .refl _
  | cons a rest ih =>
    cases H with
    | cons _ head tail => exact (bottom_read_remainder a.1 _ head.eval).trans (ih tail)

private theorem LooseExec.columns_no_split {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : LooseExec (Push.Scan.columns requests) E F) : ColumnReader.NoNorthSplit E F := by
  induction requests generalizing E with
  | nil => cases H; exact .refl _
  | cons a rest ih =>
    cases H with
    | cons _ head tail => exact ColumnReader.NoNorthSplit.trans head.no_split (ih tail) tail.subset

/-- Every requested quota is paid by the final simultaneous column difference.
Repeated requests for the same column are allowed. -/
private theorem LooseExec.columns_paid {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : LooseExec (Push.Scan.columns requests) E F) {a : ℕ × ℕ} (ha : a ∈ requests) :
    (F.filter fun p => p.1.val = a.1).card + a.2 ≤ (E.filter fun p => p.1.val = a.1).card := by
  induction requests generalizing E with
  | nil => exact False.elim (List.not_mem_nil ha)
  | cons b rest ih =>
    cases H with
    | @cons _ _ _ actual _ _ G _ paid head tail =>
      rcases List.mem_cons.mp ha with he | ha
      · subst a
        have hcard := Push.Scan.Instruction.read_line_card head.eval
        have hle : (F.filter fun p => p.1.val = b.1).card ≤
            (G.filter fun p => p.1.val = b.1).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ tail.subset)
        change (G.filter fun p => p.1.val = b.1).card + actual =
          (E.filter fun p => p.1.val = b.1).card at hcard
        omega
      · have hp := ih tail ha
        have hle : (G.filter fun p => p.1.val = a.1).card ≤
            (E.filter fun p => p.1.val = a.1).card :=
          Finset.card_le_card (Finset.filter_subset_filter _ head.subset)
        omega

/-- The exact whole-run read certified for one source column. -/
private theorem LooseExec.column_read {requests : List (ℕ × ℕ)} {E F : Finset (Cell w h)}
    (H : LooseExec (Push.Scan.columns requests) E F) (x : ℕ) :
    ExactNorthRead (E.filter fun p => p.1.val = x) (F.filter fun p => p.1.val = x) := by
  have hr := H.columns_remainder
  have hs := H.columns_no_split
  refine ⟨Finset.filter_subset_filter _ hr.subset, ?_, ?_⟩
  · intro p hp q hq
    obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpE, hpx⟩ := Finset.mem_filter.mp hpE
    obtain ⟨hqF, hqx⟩ := Finset.mem_filter.mp hq
    by_contra hle
    have hpF' := hr.northern q hqF p hpE (Fin.ext (hpx.trans hqx.symm)) (by omega)
    exact hpF (Finset.mem_filter.mpr ⟨hpF', hpx⟩)
  · intro p hp q hq ha
    obtain ⟨hpE, hpF⟩ := Finset.mem_sdiff.mp hp
    obtain ⟨hpE, hpx⟩ := Finset.mem_filter.mp hpE
    exact hs p (Finset.mem_sdiff.mpr ⟨hpE, fun hpF' => hpF (Finset.mem_filter.mpr ⟨hpF', hpx⟩)⟩)
      q (Finset.mem_filter.mp hq).1 ha

/-- Dense quota scans provide exactly the column hypotheses used by the maximum reader. -/
theorem LooseExec.ofQuotas_readout (quotas : List ℕ) {E F : Finset (Cell w h)}
    (H : LooseExec (Push.Scan.columns (Push.Scan.ofQuotas quotas)) E F) (x : ℕ) :
    ExactNorthRead (E.filter fun p => p.1.val = x) (F.filter fun p => p.1.val = x) ∧
      quotas.getD x 0 ≤ ((E.filter fun p => p.1.val = x) \ (F.filter fun p => p.1.val = x)).card := by
  have hr := H.column_read x
  refine ⟨hr, ?_⟩
  by_cases hx : x < quotas.length
  · have hpaid := H.columns_paid (Push.Scan.ofQuotas_mem quotas ⟨x, hx⟩)
    rw [List.getD_eq_getElem _ _ hx, Finset.card_sdiff_of_subset hr.subset]
    change (F.filter fun p => p.1.val = x).card + quotas[x] ≤
      (E.filter fun p => p.1.val = x).card at hpaid
    omega
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Nat.zero_le _

end PushPuzzle.PushPush.WholeScan

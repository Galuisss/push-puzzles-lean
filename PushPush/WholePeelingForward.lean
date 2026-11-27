/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.WholePeeling

/-! Selected whole-run source continuations lift while all auxiliary rows are fully consumed. -/

@[expose] public section
namespace PushPuzzle.PushPush.Cyclic

open PushFS (Cell Direction)
open Push.Cyclic
open WholeScan

private theorem frame_aux_row (r : Push.ColumnScan.Input)
    (E : Finset (Cell r.width r.height))
    (A : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    {row : ℕ} (hrow : r.height ≤ row) :
    ((E.map (sourceEmbedding r) ∪ A).filter fun q => q.2.val = row) =
      A.filter fun q => q.2.val = row := by
  ext q
  simp only [Finset.mem_filter, Finset.mem_union]
  constructor
  · rintro ⟨hq | hq, hy⟩
    · obtain ⟨p, _, rfl⟩ := Finset.mem_map.mp hq
      have hp := p.2.isLt
      change p.2.val = row at hy
      omega
    · exact ⟨hq, hy⟩
  · exact fun ⟨hq, hy⟩ => ⟨Or.inr hq, hy⟩

private theorem auxiliaryRows_nodup (r : Push.ColumnScan.Input) : (auxiliaryRows r).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro i j he
  change r.height + i = r.height + j at he
  omega

private theorem paddingRows_nodup (r : Push.ColumnScan.Input) : (paddingRows r).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro i j he
  change (wideReader r).outputHeight + i = (wideReader r).outputHeight + j at he
  omega

private theorem auxiliaryRows_lower (r : Push.ColumnScan.Input) {row : ℕ}
    (hr : row ∈ auxiliaryRows r) : r.height ≤ row := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  omega

private theorem paddingRows_lower (r : Push.ColumnScan.Input) {row : ℕ}
    (hr : row ∈ paddingRows r) : r.height ≤ row := by
  obtain ⟨j, _, rfl⟩ := List.mem_map.mp hr
  have hh : r.height ≤ (wideReader r).outputHeight := by
    change r.height ≤ r.height + (wideReader r).length
    omega
  omega

private theorem paddedUnturned_complete (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    {E F : Finset (Cell r.width r.height)}
    (D : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hdata : sourceData r D = E)
    (hrows : ∀ q ∈ D, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hstock : ∀ row ∈ auxiliaryRows r, r.width + 2 ≤ (D.filter fun q => q.2.val = row).card)
    (H : LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ tail) E F) :
    LooseExec (paddedUnturned r rows tail) D (F.map (sourceEmbedding r)) := by
  obtain ⟨K, hread, htail⟩ := (LooseExec.append_iff _ _ _ _).mp H
  let A := auxData r D
  let D₁ := K.map (sourceEmbedding r) ∪ A
  have hdecomp : D = E.map (sourceEmbedding r) ∪ A := by
    rw [source_data_decomposition r D hrows, hdata]
  have hreadLift := hread.source_lift r _ A (by
    intro instruction hi
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hi
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
    intro q hq he
    have hj : j.val < r.height := j.isLt.trans_eq hlen
    have hy := (Finset.mem_filter.mp hq).2
    change q.2.val = j.val at he
    omega)
  rw [← hdecomp] at hreadLift
  have hcleanup := LooseExec.full_rows (auxiliaryRows r) D₁ (auxiliaryRows_nodup r) (by
    intro row hr
    have hlo := auxiliaryRows_lower r hr
    have hd : (D₁.filter fun q => q.2.val = row) = D.filter fun q => q.2.val = row := by
      rw [hdecomp, frame_aux_row r E A hlo]
      exact frame_aux_row r K A hlo
    rw [hd]
    exact hstock row hr)
  let D₂ := D₁.filter fun q => q.2.val ∉ auxiliaryRows r
  have hpadding := LooseExec.full_rows (quota := 0) (paddingRows r) D₂ (paddingRows_nodup r)
    (by intro row hr; exact Nat.zero_le _)
  have hend : (D₂.filter fun q => q.2.val ∉ paddingRows r) = K.map (sourceEmbedding r) := by
    ext q
    constructor
    · intro hq
      obtain ⟨hq, hpad⟩ := Finset.mem_filter.mp hq
      obtain ⟨hq, haux⟩ := Finset.mem_filter.mp hq
      rcases Finset.mem_union.mp hq with hq | hq
      · exact hq
      · have hy := (Finset.mem_filter.mp hq).2
        by_cases hw : q.2.val < (wideReader r).outputHeight
        · exact False.elim (haux (List.mem_map.mpr
            ⟨q.2.val - r.height, List.mem_range.mpr (by omega), by omega⟩))
        · exact False.elim (hpad (List.mem_map.mpr
            ⟨q.2.val - (wideReader r).outputHeight, List.mem_range.mpr (by have := q.2.isLt; omega), by omega⟩))
    · intro hq
      obtain ⟨p, hp, rfl⟩ := Finset.mem_map.mp hq
      have hpBound := p.2.isLt
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_union_left _ (Finset.mem_map.mpr ⟨p, hp, rfl⟩), ?_⟩, ?_⟩
      · intro hr
        have hh := auxiliaryRows_lower r hr
        change r.height ≤ p.2.val at hh
        omega
      · intro hr
        have hh := paddingRows_lower r hr
        change r.height ≤ p.2.val at hh
        omega
  rw [hend] at hpadding
  have htailLift := htail.source_lift r _ ∅ (by
    intro instruction hi
    cases instruction <;> simp [SourceOff])
  simp only [Finset.union_empty] at htailLift
  exact ((hreadLift.append hcleanup).append hpadding).append htailLift

/-- The lifted next continuation ends with only the selected original source remainder. -/
theorem next_loose_complete (r : Push.ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Push.Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    {E F : Finset (Cell r.width r.height)}
    (D : Finset (Cell (dock r).outputWidth (dock r).outputHeight))
    (hdata : sourceData r D = E)
    (hrows : ∀ q ∈ D, q.2.val < r.height → 2 ≤ q.1.val ∧ q.1.val < r.width + 2)
    (hstock : ∀ row ∈ auxiliaryRows r, r.width + 2 ≤ (D.filter fun q => q.2.val = row).card)
    (H : LooseExec (Push.Scan.lines .west (Push.Scan.ofQuotas rows) ++ tail) E F) :
    LooseExec (Push.Scan.columns (Push.Scan.ofQuotas (nextQuotas r rows)) ++ nextTail r tail)
      (D.map (turnEmbedding (dock r).outputWidth (dock r).outputHeight))
      ((F.map (sourceEmbedding r)).map (turnEmbedding (dock r).outputWidth (dock r).outputHeight)) := by
  have hlift := paddedUnturned_complete r rows hlen tail D hdata hrows hstock H
  have hturn := hlift.turn _ (paddedUnturned_bounded r rows hlen tail hbound)
  rwa [paddedUnturned_turned r rows hlen tail] at hturn

end PushPuzzle.PushPush.Cyclic

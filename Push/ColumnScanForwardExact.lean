/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanForwardExactColumns
public import Push.ScanColumns

/-! The literal canonical reader realizes the exact static source-hole program. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS ReaderResidual

variable (r : Input)

/-- The actual reader holes cropped back to the original source coordinates. -/
@[expose] def sourceHolesAt (s : HoleState r.outputWidth r.outputHeight) : Finset (Cell r.width r.height) :=
  Finset.univ.filter fun q => r.embed q ∈ s.empty

@[simp] theorem mem_sourceHolesAt (s : HoleState r.outputWidth r.outputHeight) (q : Cell r.width r.height) :
    q ∈ r.sourceHolesAt s ↔ r.embed q ∈ s.empty := by simp [sourceHolesAt]

private theorem sourceHolesAt_sealedState : r.sourceHolesAt r.sealedState = r.initial.empty := by
  ext q
  rw [r.mem_sourceHolesAt, r.sealedState_source_columns _ q.1.isLt, r.embed_mem_empty]

private theorem sourceHolesAt_column_image (s : HoleState r.outputWidth r.outputHeight) (i : Fin r.width) :
    ((r.sourceHolesAt s).filter fun q => q.1 = i).image r.embed = r.remainingColumn s i := by
  ext q
  constructor
  · intro hq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hq
    obtain ⟨ha, hax⟩ := Finset.mem_filter.mp ha
    exact Finset.mem_filter.mpr ⟨(r.mem_sourceHolesAt s a).mp ha, congrArg Fin.val hax, a.2.isLt⟩
  · intro hq
    obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
    let a : Cell r.width r.height := (⟨q.1.val, by rw [hx]; exact i.isLt⟩, ⟨q.2.val, hy⟩)
    have he : r.embed a = q := Prod.ext (Fin.ext rfl) (Fin.ext rfl)
    exact Finset.mem_image.mpr ⟨a, Finset.mem_filter.mpr
      ⟨(r.mem_sourceHolesAt s a).mpr (he ▸ hq), Fin.ext hx⟩, he⟩

private theorem sourceHolesAt_column_card (s : HoleState r.outputWidth r.outputHeight)
    (i : Fin r.width) :
    ((r.sourceHolesAt s).filter fun q => q.1 = i).card = (r.remainingColumn s i).card := by
  rw [← r.sourceHolesAt_column_image s i, Finset.card_image_of_injective _ r.embed_injective]

private theorem sourceHolesAt_remainder (s t : HoleState r.outputWidth r.outputHeight)
    (hrem : BottomRemainder (HoleState.sourceRows s r.height) (HoleState.sourceRows t r.height)) :
    BottomRemainder (r.sourceHolesAt s) (r.sourceHolesAt t) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    apply (r.mem_sourceHolesAt s q).mpr
    exact (Finset.mem_filter.mp (hrem.subset
      (Finset.mem_filter.mpr ⟨(r.mem_sourceHolesAt t q).mp hq, q.2.isLt⟩))).1
  · intro p hp q hq hx hy
    apply (r.mem_sourceHolesAt t q).mpr
    exact (Finset.mem_filter.mp (hrem.northern (r.embed p)
      (Finset.mem_filter.mpr ⟨(r.mem_sourceHolesAt t p).mp hp, p.2.isLt⟩) (r.embed q)
      (Finset.mem_filter.mpr ⟨(r.mem_sourceHolesAt s q).mp hq, q.2.isLt⟩)
      (by apply Fin.ext; change q.1.val = p.1.val; exact congrArg Fin.val hx)
      hy)).1

private theorem static_columns_accept
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas)) r.initial.empty := by
  apply Scan.columns_accepts _ _ (Scan.ofQuotas_nodup _)
  intro a ha
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
  let j : Fin r.width := ⟨i.val, by rw [← r.quotas_width]; exact i.isLt⟩
  have h := hquotas j
  simpa only [j, columnSources, Fin.ext_iff, List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin] using h

private theorem static_columns_card {F : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) r.initial.empty = some F)
    (i : Fin r.width) :
    (F.filter fun q => q.1 = i).card + r.quotas.getD i.val 0 = (r.columnSources i).card := by
  let j : Fin r.quotas.length := ⟨i.val, by rw [r.quotas_width]; exact i.isLt⟩
  have h := Scan.columns_card (Scan.ofQuotas_nodup _) heval (Scan.ofQuotas_mem r.quotas j)
  simpa only [j, columnSources, Fin.ext_iff, List.getD_eq_getElem _ _ j.isLt, Fin.getElem_fin] using h

private theorem sealed_source_rows (q : Cell r.outputWidth r.outputHeight)
    (hq : q ∈ r.sealedState.empty) (hy : q.2.val < r.height) : q.1.val < r.width := by
  have hlen := r.length_ge_seven
  have hh := r.height_pos
  have hlanding : q ≠ r.landing := by
    intro he
    have hv := congrArg (fun p => p.2.val) he
    change q.2.val = r.height - 1 + r.length - 2 at hv
    omega
  have hfirst : q ≠ r.firstSeal := by
    intro he
    have hv := congrArg (fun p => p.2.val) he
    change q.2.val = r.height + r.length - 2 at hv
    omega
  simp only [sealedState, firstSealState, Finset.mem_insert, Finset.mem_erase,
    hlanding, hfirst, false_or] at hq
  exact (r.empty_on_source_row hq.2.2 hy).resolve_right hq.1

/-- The exact canonical remainder has no auxiliary hole on an original source row. -/
theorem compile_run_exact_source_supported
    (hcorner : r.initial.player = r.sourceCorner)
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t.toState ∧ t.player = r.target ∧
      r.room ⊆ t.empty ∧
      Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) r.initial.empty = some (r.sourceHolesAt t) ∧
      ∀ q ∈ t.empty, q.2.val < r.height → q.1.val < r.width := by
  obtain ⟨t, hr, ht, hroom, hcards, hrem⟩ := r.compile_run_exact_columns hcorner hquotas
  have hrem' := r.sourceHolesAt_remainder _ _ hrem
  rw [r.sourceHolesAt_sealedState] at hrem'
  obtain ⟨F, hF⟩ := r.static_columns_accept hquotas
  have hstatic := Scan.columns_remainder hF
  have hcard : ∀ i : Fin r.width,
      ((r.sourceHolesAt t).filter fun q => q.1 = i).card = (F.filter fun q => q.1 = i).card := by
    intro i
    rw [r.sourceHolesAt_column_card]
    exact Nat.add_right_cancel ((hcards i).trans (r.static_columns_card hF i).symm)
  have he : r.sourceHolesAt t = F := Finset.Subset.antisymm
    (hrem'.subset_of_column_card hstatic (fun i => (hcard i).le))
    (hstatic.subset_of_column_card hrem' (fun i => (hcard i).ge))
  refine ⟨t, hr, ht, hroom, he ▸ hF, ?_⟩
  intro q hq hy
  exact r.sealed_source_rows q (Finset.mem_filter.mp
    (hrem.subset (Finset.mem_filter.mpr ⟨hq, hy⟩))).1 hy

end PushPuzzle.Push.ColumnScan.Input

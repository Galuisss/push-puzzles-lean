/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseSupport

/-! Static north clearing and auxiliary cleanup leave exactly the erased data and orthogonal inventory. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS CornerDock.Backup

private theorem data_decomposition (r : ColumnScan.Input)
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)) :
    E = (dataHoles r E).image (sourceCell r) ∪ (E \ Finset.univ.image (sourceCell r)) := by
  ext q
  constructor
  · intro hq
    by_cases hs : q ∈ Finset.univ.image (sourceCell r)
    · obtain ⟨p, _, rfl⟩ := Finset.mem_image.mp hs
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hq⟩, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨hq, hs⟩)
  · intro hq
    rcases Finset.mem_union.mp hq with hd | ha
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
      exact (Finset.mem_filter.mp hp).2
    · exact (Finset.mem_sdiff.mp ha).1

private theorem auxiliary_above (r : ColumnScan.Input)
    {E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)} (hs : DataSupported r E)
    (q : Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)
    (hq : q ∈ E \ Finset.univ.image (sourceCell r)) : r.height ≤ q.2.val := by
  obtain ⟨hqE, hnot⟩ := Finset.mem_sdiff.mp hq
  by_contra hy
  have hy' : q.2.val < r.height := by omega
  obtain ⟨hlo, hhi⟩ := hs q hqE hy'
  let p : Cell r.width r.height := (⟨q.1.val - 2, by omega⟩, ⟨q.2.val, hy'⟩)
  apply hnot
  apply Finset.mem_image.mpr ⟨p, Finset.mem_univ _, ?_⟩
  apply Prod.ext <;> apply Fin.ext
  · change q.1.val - 2 + 2 = q.1.val
    omega
  · rfl

/-- Backed north reads implement exact source-column erasure and leave only inventory off every source line. -/
theorem erase_cleanup_orthogonal (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (selected : Finset (Fin r.width))
    (E : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight))
    (hbackup : ∀ x : Fin r.width, ∀ i : Fin r.height, backupCell r hk x i ∈ E)
    (hstock : ∀ row : Fin (eraseDock r).outputHeight, r.height ≤ row.val →
      row.val < (wideEraseReader r).outputHeight →
        r.width + 2 ≤ (E.filter fun q => q.2 = row ∧ r.width + 3 ≤ q.1.val).card)
    (hs : DataSupported r E)
    (hsouth : ∀ q ∈ E, (wideEraseReader r).outputHeight ≤ q.2.val → q.1.val < 2) :
    ∃ F G A : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight),
      Scan.eval (eraseProgram r selected) E = some F ∧
      Scan.eval (Cyclic.rowProgram (Cyclic.auxiliaryRows r) (r.width + 2)) F = some G ∧
      G = ((dataHoles r E).filter fun p => p.1 ∉ selected).image (sourceCell r) ∪ A ∧
      ∀ q ∈ A, r.height ≤ q.2.val ∧ (q.1.val < 2 ∨ r.width + 2 ≤ q.1.val) := by
  obtain ⟨F, G, hF, hG, hdata, hsep⟩ := erase_and_cleanup r hk selected E hbackup hstock hsouth
  have hsub := (Scan.eval_subset hG).trans (Scan.eval_subset hF)
  have hsG : DataSupported r G := fun q hq hy => hs q (hsub hq) hy
  refine ⟨F, G, G \ Finset.univ.image (sourceCell r), hF, hG, ?_, ?_⟩
  · rw [← hdata]
    exact data_decomposition r G
  · intro q hq
    have hy := auxiliary_above r hsG q hq
    exact ⟨hy, hsep q (Finset.mem_sdiff.mp hq).1 hy⟩

/-- The actual wide-reader and backup path provide all hypotheses of exact erasure and orthogonal cleanup. -/
theorem compile_erase_cleanup (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (selected : Finset (Fin r.width)) {s : State r.width r.height}
    (hr : Reachable r.sourceBoard none r.initial.toState s) (hcorner : s.player = r.sourceCorner)
    {E : Finset (Cell r.width r.height)}
    (heval : Scan.eval (Scan.columns (Scan.ofQuotas r.quotas)) (holes s) = some E) :
    ∃ (t : HoleState (eraseDock r).outputWidth (eraseDock r).outputHeight)
      (F G A : Finset (Cell (eraseDock r).outputWidth (eraseDock r).outputHeight)),
      Reachable (eraseDock r).compile.board none (eraseDock r).compile.initial t.toState ∧
      t.player = (eraseDock r).target ∧
      Scan.eval (eraseProgram r selected) t.empty = some F ∧
      Scan.eval (Cyclic.rowProgram (Cyclic.auxiliaryRows r) (r.width + 2)) F = some G ∧
      G = (E.filter fun p => p.1 ∉ selected).image (sourceCell r) ∪ A ∧
      ∀ q ∈ A, r.height ≤ q.2.val ∧ (q.1.val < 2 ∨ r.width + 2 ≤ q.1.val) := by
  obtain ⟨t, ht, htp, hdata, hbackup, hstock, hs, hsouth⟩ := compile_backups_supported r hk hr hcorner heval
  obtain ⟨F, G, A, hF, hG, hdecomp, hA⟩ := erase_cleanup_orthogonal r hk selected t.empty hbackup hstock hs hsouth
  have he : dataHoles r t.empty = E := by
    ext p
    simp only [dataHoles, Finset.mem_filter, Finset.mem_univ, true_and]
    exact hdata p
  exact ⟨t, F, G, A, ht, htp, hF, hG, he ▸ hdecomp, hA⟩

end PushPuzzle.Push.CyclicErase

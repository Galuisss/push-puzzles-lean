/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanForwardExactRead
public import Push.ColumnScanForwardColumns
import all Push.ColumnScanForwardColumns

/-! Exact column inventories along the canonical concrete reader route. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS ReaderResidual

variable (r : Input)

/-- The remaining original-source rows in one column of an actual reader state. -/
@[expose] def remainingColumn (s : HoleState r.outputWidth r.outputHeight) (i : Fin r.width) :
    Finset (Cell r.outputWidth r.outputHeight) :=
  s.empty.filter fun q => q.1.val = i.val ∧ q.2.val < r.height

private theorem northSources_eq (s : HoleState r.outputWidth r.outputHeight)
    (i : Fin r.width) (hx : s.player.1.val = i.val) :
    HoleState.northSources s r.height = r.remainingColumn s i := by
  ext q
  simp only [HoleState.northSources, remainingColumn, Finset.mem_filter, Fin.ext_iff, hx]

private theorem remainingColumn_frame (s t : HoleState r.outputWidth r.outputHeight) (i : Fin r.width)
    (hf : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
      (q ∈ t.empty ↔ q ∈ s.empty)) : r.remainingColumn t i = r.remainingColumn s i := by
  ext q
  simp only [remainingColumn, Finset.mem_filter]
  by_cases hx : q.1.val = i.val
  · rw [hf q hx]
  · simp only [hx, false_and, and_false]

private theorem read_needle_exact (i : Fin r.width)
    (hquota : r.quotas.getD i.val 0 ≤ (r.columnSources i).card)
    (s : HoleState r.outputWidth r.outputHeight) (hp : s.player = r.needle i)
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧
      t.player.1 = s.player.1 ∧ t.player.2.val + r.quotas.getD i.val 0 = s.player.2.val ∧
      (∀ q : Cell r.outputWidth r.outputHeight, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      (r.remainingColumn t i).card + r.quotas.getD i.val 0 = (r.columnSources i).card ∧
      BottomRemainder (HoleState.sourceRows s r.height) (HoleState.sourceRows t r.height) := by
  have hx : s.player.1.val = i.val := by rw [hp]; rfl
  have hy : s.player.2.val = r.needleLevel i := by rw [hp]; rfl
  have hspace : r.height + r.quotas.getD i.val 0 < s.player.2.val := by
    have hsmall : (r.columnSources i).card ≤ r.sourceHoles :=
      Finset.card_le_card (Finset.filter_subset _ _)
    have hfar := r.needle_far_south i
    change r.height + max r.sourceHoles r.width < r.needleLevel i at hfar
    have := Nat.le_max_left r.sourceHoles r.width
    omega
  have hcount : r.quotas.getD i.val 0 ≤ (HoleState.northSources s r.height).card := by
    rw [r.northSources_card i s hx hc]
    exact hquota
  obtain ⟨t, ht, htx, hty, hf, hcard, hrem⟩ := HoleState.read_north_exact s r.height
    (r.quotas.getD i.val 0) hspace hcount (by
      intro q hqx hlo hhi hq
      have hqx' : q.1.val = i.val := (congrArg Fin.val hqx).trans hx
      exact r.column_gap i q hqx' hlo (by omega) ((hc q hqx').mp hq))
    r.compile.board r.compile.walls_empty
  rw [r.northSources_eq t i ((congrArg Fin.val htx).trans hx), r.northSources_card i s hx hc] at hcard
  exact ⟨t, ht, htx, hty, hf, hcard, hrem⟩

private theorem advance_column_exact (i : Fin r.width)
    (hquota : r.quotas.getD i.val 0 ≤ (r.columnSources i).card)
    (s : HoleState r.outputWidth r.outputHeight)
    (hx : s.player.1.val = i.val + 1) (hy : s.player.2.val = r.readLevel (i.val + 1))
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧
      t.player.1.val = i.val ∧ t.player.2.val = r.readLevel i.val ∧
      (∀ q : Cell r.outputWidth r.outputHeight, q.1.val ≠ i.val → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      (r.remainingColumn t i).card + r.quotas.getD i.val 0 = (r.columnSources i).card ∧
      BottomRemainder (HoleState.sourceRows s r.height) (HoleState.sourceRows t r.height) := by
  have hm : r.needle i ∈ s.empty := (hc _ rfl).mpr (r.needle_mem i)
  let a := s.walk (r.needle i) hm
  have hwalk : Move r.compile.board none .west s.toState a.toState :=
    s.walk_move hm (by
      change (r.needle i).1.val + 1 = s.player.1.val ∧ (r.needle i).2 = s.player.2
      exact ⟨hx.symm, Fin.ext hy.symm⟩) r.compile.board r.compile.walls_empty none
  obtain ⟨t, ht, htx, hty, hf, hc, hrem⟩ := r.read_needle_exact i hquota a rfl hc
  refine ⟨t, (Relation.ReflTransGen.single ⟨.west, hwalk⟩).trans ht,
    congrArg Fin.val htx, Nat.add_right_cancel (hty.trans (r.readLevel_succ i)), ?_, hc, hrem⟩
  intro q hq
  exact hf q (fun he => hq (congrArg Fin.val he))

private theorem read_columns_exact
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card)
    (k : ℕ) (hk : k ≤ r.width) (s : HoleState r.outputWidth r.outputHeight)
    (hx : s.player.1.val = k) (hy : s.player.2.val = r.readLevel k)
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val < k →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧
      t.player.1.val = 0 ∧ t.player.2.val = r.targetLevel ∧
      (∀ q : Cell r.outputWidth r.outputHeight, k ≤ q.1.val → (q ∈ t.empty ↔ q ∈ s.empty)) ∧
      (∀ i : Fin r.width, i.val < k →
        (r.remainingColumn t i).card + r.quotas.getD i.val 0 = (r.columnSources i).card) ∧
      BottomRemainder (HoleState.sourceRows s r.height) (HoleState.sourceRows t r.height) := by
  induction k generalizing s with
  | zero =>
    exact ⟨s, .refl, hx, by simpa only [readLevel_zero] using hy,
      fun _ _ => Iff.rfl, by intro i hi; omega, .refl _⟩
  | succ k ih =>
    let i : Fin r.width := ⟨k, by omega⟩
    obtain ⟨t, hread, htx, hty, hframe, hcard, hrem⟩ :=
      r.advance_column_exact i (hquotas i) s hx hy
        (fun q hq => hc q (by change q.1.val = k at hq; omega))
    obtain ⟨u, hrun, hux, huy, hout, hcards, huremain⟩ := ih (by omega) t
      htx hty (by intro q hq; exact (hframe q (by dsimp [i]; omega)).trans (hc q (by omega)))
    refine ⟨u, hread.trans hrun,
      hux, huy, ?_, ?_, hrem.trans huremain⟩
    · intro q hq
      apply (hout q (by omega)).trans
      exact hframe q (by dsimp [i]; omega)
    · intro j hj
      by_cases hjk : j.val < k
      · exact hcards j hjk
      · have hji : j = i := Fin.ext (by dsimp [i]; omega)
        subst j
        rw [r.remainingColumn_frame t u i (fun q hq => hout q (by dsimp [i] at hq; omega))]
        exact hcard

/-- The canonical route pays each source-column quota exactly and preserves the full eastern room. -/
theorem compile_run_exact_columns
    (hcorner : r.initial.player = r.sourceCorner)
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t.toState ∧ t.player = r.target ∧
      r.room ⊆ t.empty ∧
      (∀ i : Fin r.width, (r.remainingColumn t i).card + r.quotas.getD i.val 0 =
        (r.columnSources i).card) ∧
      BottomRemainder (HoleState.sourceRows r.sealedState r.height) (HoleState.sourceRows t r.height) := by
  obtain ⟨t, hr, hx, hy, hframe, hcards, hrem⟩ := r.read_columns_exact hquotas r.width
    (Nat.le_refl _) r.sealedState rfl (by
      change r.firstLevel = r.firstLevel - (r.quotas.drop r.width).sum
      rw [← r.quotas_width, List.drop_length, List.sum_nil, Nat.sub_zero])
    r.sealedState_source_columns
  refine ⟨t, (r.sealedState_reachable hcorner).trans hr, ?_, ?_,
    fun i => hcards i i.isLt, hrem⟩
  · exact Prod.ext (Fin.ext hx) (Fin.ext hy)
  · intro q hq
    have hqx := (Finset.mem_filter.mp hq).2.1
    apply (hframe q (by omega)).mpr
    apply (r.sealedState_off_separator q (by omega)).mpr
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq))

end PushPuzzle.Push.ColumnScan.Input

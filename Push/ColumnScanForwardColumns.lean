/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanForwardRead
import Mathlib.Data.List.GetD

/-! A complete right-to-left column-reader execution on the actual compiled board. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS

variable (r : Input)

/-- The original source holes in one designated source column. -/
def columnSources (i : Fin r.width) : Finset (Cell r.width r.height) :=
  r.initial.empty.filter fun q => q.1 = i

private theorem needle_mem (i : Fin r.width) : r.needle i ∈ r.empty := by
  apply Finset.mem_union_right
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- The two seal pushes preserve every other column exactly. -/
theorem sealedState_off_separator (q : Cell r.outputWidth r.outputHeight)
    (hx : q.1.val ≠ r.width) : q ∈ r.sealedState.empty ↔ q ∈ r.empty := by
  have hd : q ≠ r.door := by
    intro he
    have := congrArg (fun q => q.1.val) he
    change q.1.val = r.width at this
    omega
  have hu : q ≠ r.upper := by
    intro he
    have := congrArg (fun q => q.1.val) he
    change q.1.val = r.width at this
    omega
  have hf : q ≠ r.firstSeal := by
    intro he
    have := congrArg (fun q => q.1.val) he
    change q.1.val = r.width at this
    omega
  have hl : q ≠ r.landing := by
    intro he
    have := congrArg (fun q => q.1.val) he
    change q.1.val = r.width at this
    omega
  simp [sealedState, firstSealState, hd, hu, hf, hl]

/-- The two seal pushes preserve every original source column exactly. -/
theorem sealedState_source_columns (q : Cell r.outputWidth r.outputHeight)
    (hx : q.1.val < r.width) : q ∈ r.sealedState.empty ↔ q ∈ r.empty :=
  r.sealedState_off_separator q (by omega)

private theorem column_gap (i : Fin r.width) (q : Cell r.outputWidth r.outputHeight)
    (hx : q.1.val = i.val) (hlo : r.height ≤ q.2.val)
    (hhi : q.2.val < r.needleLevel i) : q ∉ r.empty := by
  intro hq
  rw [empty, Finset.mem_union] at hq
  rcases hq with hs | ha
  · obtain ⟨a, _, ha⟩ := Finset.mem_image.mp hs
    have hy := congrArg (fun q => q.2.val) ha
    have := a.2.isLt
    change a.2.val = q.2.val at hy
    omega
  · simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with (((he | he | he) | he) | he)
    · have hxx := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at hxx
      have := i.isLt
      omega
    · have hxx := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at hxx
      have := i.isLt
      omega
    · have hxx := congrArg (fun q => q.1.val) he
      change q.1.val = r.width at hxx
      have := i.isLt
      omega
    · have hxx := (Finset.mem_filter.mp he).2.1
      have := i.isLt
      omega
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he
      have hxx := congrArg (fun q => q.1.val) hj
      have hij : j = i := Fin.ext (hxx.trans hx)
      subst j
      have hy := congrArg (fun q => q.2.val) hj
      change r.needleLevel i = q.2.val at hy
      omega

private theorem northSources_card (i : Fin r.width)
    (s : PushS.HoleState r.outputWidth r.outputHeight)
    (hx : s.player.1.val = i.val)
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    (HoleState.northSources s r.height).card = (r.columnSources i).card := by
  symm
  apply Finset.card_bij (fun q _ => r.embed q)
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    apply Finset.mem_filter.mpr
    refine ⟨(hc (r.embed q) (by simp only [embed, hq'.2])).mpr
      ((r.embed_mem_empty q).mpr hq'.1), ?_, q.2.isLt⟩
    apply Fin.ext
    exact (congrArg Fin.val hq'.2).trans hx.symm
  · intro a ha b hb hab
    exact r.embed_injective hab
  · intro q hq
    have hq' := Finset.mem_filter.mp hq
    have hqx : q.1.val = i.val := (congrArg Fin.val hq'.2.1).trans hx
    let a : Cell r.width r.height :=
      (⟨q.1.val, by rw [hqx]; exact i.isLt⟩, ⟨q.2.val, hq'.2.2⟩)
    have he : r.embed a = q := by apply Prod.ext <;> apply Fin.ext <;> rfl
    refine ⟨a, Finset.mem_filter.mpr ⟨?_, Fin.ext hqx⟩, he⟩
    apply (r.embed_mem_empty a).mp
    rw [he]
    exact (hc q hqx).mp hq'.1

private theorem read_needle (i : Fin r.width)
    (hquota : r.quotas.getD i.val 0 ≤ (r.columnSources i).card)
    (s : PushS.HoleState r.outputWidth r.outputHeight) (hp : s.player = r.needle i)
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    ∃ t : PushS.HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧
      t.player.1 = s.player.1 ∧ t.player.2.val + r.quotas.getD i.val 0 = s.player.2.val ∧
      (∀ q : Cell r.outputWidth r.outputHeight, q.1 ≠ s.player.1 → (q ∈ t.empty ↔ q ∈ s.empty)) := by
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
  apply HoleState.read_north s r.height (r.quotas.getD i.val 0) hspace hcount ?_
    r.compile.board r.compile.walls_empty
  intro q hqx hlo hhi hq
  have hqx' : q.1.val = i.val := (congrArg Fin.val hqx).trans hx
  exact r.column_gap i q hqx' hlo (by omega) ((hc q hqx').mp hq)

private theorem read_columns
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card)
    (k : ℕ) (hk : k ≤ r.width) (s : PushS.HoleState r.outputWidth r.outputHeight)
    (hx : s.player.1.val = k) (hy : s.player.2.val = r.readLevel k)
    (hc : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val < k →
      (q ∈ s.empty ↔ q ∈ r.empty)) :
    ∃ t : PushS.HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none s.toState t.toState ∧
      t.player.1.val = 0 ∧ t.player.2.val = r.targetLevel ∧
      ∀ q : Cell r.outputWidth r.outputHeight, k ≤ q.1.val →
        (q ∈ t.empty ↔ q ∈ s.empty) := by
  induction k generalizing s with
  | zero =>
    exact ⟨s, .refl, hx, by simpa only [readLevel_zero] using hy, fun _ _ => Iff.rfl⟩
  | succ k ih =>
    let i : Fin r.width := ⟨k, by omega⟩
    have hm : r.needle i ∈ s.empty :=
      (hc (r.needle i) (by change k < k + 1; omega)).mpr (r.needle_mem i)
    let a := s.walk (r.needle i) hm
    have hwalk : Move r.compile.board none .west s.toState a.toState :=
      s.walk_move hm (by
        change (r.needle i).1.val + 1 = s.player.1.val ∧ (r.needle i).2 = s.player.2
        refine ⟨hx.symm, Fin.ext ?_⟩
        exact hy.symm) r.compile.board r.compile.walls_empty none
    have hcolumn : ∀ q : Cell r.outputWidth r.outputHeight, q.1.val = i.val →
        (q ∈ a.empty ↔ q ∈ r.empty) := fun q hq => hc q (by change q.1.val = k at hq; omega)
    obtain ⟨t, hread, htx, hty, hframe⟩ := r.read_needle i (hquotas i) a rfl hcolumn
    have hty' : t.player.2.val = r.readLevel k :=
      Nat.add_right_cancel (hty.trans (r.readLevel_succ i))
    obtain ⟨u, hrun, hux, huy, hout⟩ := ih (by omega) t
      (by exact (congrArg Fin.val htx)) hty' (by
        intro q hq
        have hne : q.1 ≠ a.player.1 := by
          intro he
          have hv := congrArg Fin.val he
          change q.1.val = k at hv
          omega
        exact (hframe q hne).trans (hc q (by omega)))
    refine ⟨u, ((Relation.ReflTransGen.single ⟨.west, hwalk⟩).trans hread).trans hrun, hux, huy, ?_⟩
    intro q hq
    apply (hout q (by omega)).trans
    exact hframe q (by intro he; have := congrArg Fin.val he; change q.1.val = k at this; omega)

/-- The concrete successful reader route preserves every hole of its eastern room. -/
private theorem compile_run_of_column_quotas
    (hcorner : r.initial.player = r.sourceCorner)
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card) :
    ∃ t : HoleState r.outputWidth r.outputHeight,
      Reachable r.compile.board none r.compile.initial t.toState ∧ t.player = r.target ∧
      r.room ⊆ t.empty := by
  obtain ⟨t, hr, hx, hy, hframe⟩ := r.read_columns hquotas r.width (Nat.le_refl _) r.sealedState
    rfl (by
      change r.firstLevel = r.firstLevel - (r.quotas.drop r.width).sum
      rw [← r.quotas_width, List.drop_length, List.sum_nil, Nat.sub_zero])
    (r.sealedState_source_columns)
  refine ⟨t, (r.sealedState_reachable hcorner).trans hr, ?_, ?_⟩
  · apply Prod.ext <;> apply Fin.ext
    · exact hx
    · exact hy
  · intro q hq
    have hqx := (Finset.mem_filter.mp hq).2.1
    apply (hframe q (by omega)).mpr
    apply (r.sealedState_off_separator q (by omega)).mpr
    exact Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq))

/-- Paying every original column quota gives a concrete successful ordinary-reader run. -/
theorem compile_solvable_of_column_quotas
    (hcorner : r.initial.player = r.sourceCorner)
    (hquotas : ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (r.columnSources i).card) :
    r.compile.Solvable := by
  obtain ⟨t, hr, ht, _⟩ := r.compile_run_of_column_quotas hcorner hquotas
  exact ⟨t.toState, hr, ht⟩

end PushPuzzle.Push.ColumnScan.Input

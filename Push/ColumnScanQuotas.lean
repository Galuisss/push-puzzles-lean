/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanNoReturn
public import Push.ColumnScanReadGuard
public import Push.ReadBudgetProjection
public import Push.ReaderResidual

/-! Every column quota is paid by holes of the same committed source bitmap. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier SealProjection

variable (r : ColumnScan.Input)

/-- At commitment, each source column contains only its original needle and its live source holes. -/
private theorem landing_column_split
    {s finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (i : Fin r.width) :
    ColumnReadBudget.Split (0 - (r.height : ℤ) + 1) (-(r.needleLevel i : ℤ))
      (columnHoles i.val 0 s) := by
  intro z hz
  obtain ⟨q, hq, hx, hcoord⟩ := mem_columnHoles.mp hz
  by_cases hy : q.2.val < r.height
  · right
    dsimp [coordinate] at hcoord
    omega
  · obtain ⟨j, hj⟩ := (r.before_south_exact hpre hsf hfx hfy (by omega) (by omega)).mp hq
    have hji : j = i := by
      apply Fin.ext
      have := congrArg (fun q => q.1.val) hj
      change j.val = q.1.val at this
      omega
    rw [hji] at hj
    left
    have hqy := congrArg (fun q => q.2.val) hj
    change r.needleLevel i = q.2.val at hqy
    dsimp [coordinate] at hcoord
    omega

/-- Any physical progress toward the next needle spends holes of the committed source column. -/
private theorem landing_column_advance_budget
    {s t finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hland : s.player = r.landing) (i : Fin r.width)
    (hread : Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel) s t)
    (htf : Reachable r.compile.board none t finish)
    (htx : t.player.1.val = i.val) (hty : r.height ≤ t.player.2.val) :
    (r.needleLevel i : ℤ) - t.player.2.val +
      ((ReadBudgetProjection.sourceCells i.val r.height t).card : ℤ) ≤
      ((ReadBudgetProjection.sourceCells i.val r.height s).card : ℤ) := by
  have hpreN : Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel)
      r.initialState.toState s :=
    Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm.1, fun hx => hm.2 (by omega)⟩) _ _ hpre
  have hguarded : Relation.ReflTransGen
      (ReadBudgetProjection.GuardedStep r.compile.board none i.val 0 (0 - (r.height : ℤ) + 1)) s t := by
    apply Path.enrich hread
    intro a b hsa hm hbt
    have hsa' : Reachable r.compile.board none s a :=
      Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hsa
    have hsb' := hsa'.tail hm.1
    have hbf : Reachable r.compile.board none b finish :=
      (Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hbt).trans htf
    refine ⟨⟨hm.1.choose, hm.1.choose_spec,
      r.before_next_move_guard i (hpreN.trans hsa) hm.1.choose_spec
        (r.landing_no_return hpre hsf hfx hfy hland hsb') hbf hfx hfy⟩, ?_, ?_⟩
    · apply ReadBudgetProjection.outside_iff.mpr
      intro hx
      exact r.landing_no_return hpre hsf hfx hfy hland hsa' (by rw [hx]; exact i.isLt)
    · apply ReadBudgetProjection.outside_iff.mpr
      intro hx
      exact r.landing_no_return hpre hsf hfx hfy hland hsb' (by rw [hx]; exact i.isLt)
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hpre
  have hv := Reachable.valid hreach r.compile.initial_valid
  have hb := ReadBudgetProjection.player_advance_budget (w := r.outputWidth) (h := r.outputHeight) hguarded hv
    (r.landing_column_split hpre hsf hfx hfy i) htx hty
  dsimp [coordinate] at hb
  omega

private theorem landing_column_advance_le
    {s t finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hland : s.player = r.landing) (i : Fin r.width)
    (hread : Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel) s t)
    (htf : Reachable r.compile.board none t finish)
    (htx : t.player.1.val = i.val) (hty : r.height ≤ t.player.2.val) :
    (r.needleLevel i : ℤ) - t.player.2.val ≤
      ((ReadBudgetProjection.sourceCells i.val r.height s).card : ℤ) := by
  have := r.landing_column_advance_budget hpre hsf hfx hfy hland i hread htf htx hty
  omega

private theorem landing_column_endpoint
    {s finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : finish.player.2.val = r.targetLevel)
    (hland : s.player = r.landing) (i : Fin r.width) :
    ∃ u : State r.outputWidth r.outputHeight,
      Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel) s u ∧
      Reachable r.compile.board none u finish ∧
      u.player.1.val = i.val ∧ u.player.2.val = r.readLevel i.val := by
  by_cases hi : i.val = 0
  · refine ⟨finish, ?_, .refl, by omega, ?_⟩
    · exact Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm, fun hx => by omega⟩) _ _ hsf
    · rw [hi, r.readLevel_zero]
      exact hfy
  · have hsNorth : North i.val r.targetLevel s := by
      intro hx
      have := congrArg (fun q => q.1.val) hland
      change s.player.1.val = r.width at this
      have := i.isLt
      omega
    have hfSouth : ¬North i.val r.targetLevel finish := by
      intro h
      have := h (by omega)
      omega
    obtain ⟨u, v, hsu, hu, huv, hv, hvf⟩ := Path.first_exit
      (α := State r.outputWidth r.outputHeight) hsf hsNorth hfSouth
    have hpreN : Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel)
        r.initialState.toState u :=
      (Relation.ReflTransGen.mono (fun _ _ hm => ⟨hm.1, fun hx => hm.2 (by omega)⟩)
        _ _ hpre).trans hsu
    have hvSouth : v.player.1.val < i.val ∧ r.targetLevel ≤ v.player.2.val := by
      by_contra h
      apply hv
      intro hx
      omega
    have hcut : i.val ≤ r.width := by have := i.isLt; omega
    obtain ⟨j, hj, hp, hb⟩ := r.first_south_walk hcut hpreN huv hvSouth.1 hvSouth.2 hvf hfx hfy.ge
    obtain ⟨hd, hux, _⟩ := r.first_south_direction hcut hpreN huv.choose_spec hvSouth.1 hvSouth.2
    have ha := players_adjacent huv.choose_spec
    rw [hd] at ha
    have hpy := congrArg (fun q => q.2.val) hp
    change r.needleLevel j = v.player.2.val at hpy
    rw [r.needleLevel_eq_readLevel, hj] at hpy
    have hay := congrArg Fin.val ha.2
    exact ⟨u, hsu, (Relation.ReflTransGen.single huv).trans hvf, hux, by omega⟩

/-- All quotas hold simultaneously in the single source bitmap at the committed landing. -/
theorem landing_column_quotas
    {s finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : finish.player.2.val = r.targetLevel)
    (hland : s.player = r.landing) :
    ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤
      (ReadBudgetProjection.sourceCells i.val r.height s).card := by
  intro i
  obtain ⟨u, hread, huf, hux, huy⟩ := r.landing_column_endpoint hpre hsf hfx hfy hland i
  have hsu : Reachable r.compile.board none s u :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hread
  have hsource := r.landing_no_return hpre hsf hfx hfy.ge hland hsu (by rw [hux]; exact i.isLt)
  have hbudget := r.landing_column_advance_le hpre hsf hfx hfy.ge hland i hread huf hux hsource
  have hlevel := (r.needleLevel_eq_readLevel i).trans (r.readLevel_succ i)
  omega

private theorem landing_column_remainder_le
    {s u finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hland : s.player = r.landing) (hsu : Reachable r.compile.board none s u)
    (huf : Reachable r.compile.board none u finish) (i : Fin r.width) :
    (ReadBudgetProjection.sourceCells i.val r.height finish).card ≤
      (ReadBudgetProjection.sourceCells i.val r.height u).card := by
  have hpath : Relation.ReflTransGen (fun a b => Step r.compile.board none a b ∧
      (b.player.1.val < r.width → r.height ≤ b.player.2.val)) u finish := by
    apply Path.enrich huf
    intro a b hua hm hbf
    exact ⟨hm, r.landing_no_return hpre hsf hfx hfy hland ((hsu.trans hua).tail hm)⟩
  have hsub := ReaderResidual.reachable_source_subset hpath
  apply Finset.card_le_card
  intro q hq
  obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
  have hh := hsub (Finset.mem_filter.mpr ⟨hq, by rw [hx]; exact i.isLt, hy⟩)
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hh).1, hx, hy⟩

/-- The final residual source has lost at least the prescribed quota from every original column. -/
theorem landing_column_consumed_quotas
    {s finish : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : finish.player.2.val = r.targetLevel)
    (hland : s.player = r.landing) :
    ∀ i : Fin r.width, r.quotas.getD i.val 0 +
      (ReadBudgetProjection.sourceCells i.val r.height finish).card ≤
        (ReadBudgetProjection.sourceCells i.val r.height s).card := by
  intro i
  obtain ⟨u, hread, huf, hux, huy⟩ := r.landing_column_endpoint hpre hsf hfx hfy hland i
  have hsu : Reachable r.compile.board none s u :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hread
  have hout := r.landing_no_return hpre hsf hfx hfy.ge hland hsu (by rw [hux]; exact i.isLt)
  have hb := r.landing_column_advance_budget hpre hsf hfx hfy.ge hland i hread huf hux hout
  have hlevel := (r.needleLevel_eq_readLevel i).trans (r.readLevel_succ i)
  have hrest := r.landing_column_remainder_le hpre hsf hfx hfy.ge hland hsu huf i
  omega

end PushPuzzle.Push.ColumnScan.Input

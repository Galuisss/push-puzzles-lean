/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanNoReturn
public import Push.ReaderResidual
public import Push.ColumnScanResidualScan

/-! Every committed-reader source deletion is one exact bottom-first column read. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier ReflectedFrontier ReaderResidual

variable (r : ColumnScan.Input)

private theorem north_run_maximal {s : State r.outputWidth r.outputHeight} {n : ℕ}
    (run : @Run r.outputWidth r.outputHeight r.compile.board .north s n)
    (hs : r.height ≤ s.player.2.val)
    {p : Cell r.outputWidth r.outputHeight} (hp : p ∈ source r.width r.height s)
    (hx : p.1 = (run.cell ⟨n + 1, by omega⟩).1) :
    p.2.val ≤ (run.cell ⟨n + 1, by omega⟩).2.val := by
  by_contra hy
  have hpy := (Finset.mem_filter.mp hp).2.2
  have hend := run.position ⟨n + 1, by omega⟩
  have hlend := run.lane ⟨n + 1, by omega⟩
  simp only [Direction.position, Direction.lane] at hend hlend
  let k := s.player.2.val - p.2.val
  have hk : 0 < k ∧ k ≤ n := by dsimp [k]; omega
  let i : Fin (n + 2) := ⟨k, by omega⟩
  have hpos := run.position i
  have hlane := run.lane i
  simp only [Direction.position, Direction.lane] at hpos hlane
  have he : run.cell i = p := by
    apply Prod.ext <;> apply Fin.ext
    · have hxp := congrArg Fin.val hx
      omega
    · change -((run.cell i).2.val : ℤ) = -(s.player.2.val : ℤ) + (k : ℤ) at hpos
      dsimp [k] at hpos
      omega
  have hbox : p ∈ s.boxes := he ▸ run.occupied_at i hk.1 hk.2
  exact (mem_holes _).mp (Finset.mem_filter.mp hp).1 hbox

section Committed
variable {start finish : State r.outputWidth r.outputHeight}
  (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
    r.initialState.toState start) (hsf : Reachable r.compile.board none start finish)
  (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
  (hland : start.player = r.landing)

include hpre hsf hfx hfy hland

/-- The whole right side of every source row remains occupied after commitment. -/
private theorem landing_source_right_full {s : State r.outputWidth r.outputHeight}
    (hst : Reachable r.compile.board none start s) (p : Cell r.outputWidth r.outputHeight)
    (hx : r.width ≤ p.1.val) (hy : p.2.val < r.height) : p ∈ s.boxes := by
  have hreach : Reachable r.compile.board none r.compile.initial start :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hpre
  have hnow := hreach.trans hst
  by_cases hx' : r.width < p.1.val
  · exact r.east_full hnow p hx' hy
  · by_cases hy' : p.2.val + 1 < r.height
    · exact r.northeast_full hnow p hx hy'
    · have he : p = r.door := by
        apply Prod.ext <;> apply Fin.ext
        · dsimp [door]
          omega
        · dsimp [door]
          have := r.height_pos
          omega
      exact he ▸ r.reachable_door_full hreach hst (r.landing_door_occupied hpre hsf hfx hfy hland)

/-- Every player position after commitment lies below every original source row. -/
theorem landing_player_below_source {s : State r.outputWidth r.outputHeight}
    (hst : Reachable r.compile.board none start s) : r.height ≤ s.player.2.val := by
  by_contra hy
  by_cases hx : s.player.1.val < r.width
  · have := r.landing_no_return hpre hsf hfx hfy hland hst hx
    omega
  · have hbox := r.landing_source_right_full hpre hsf hfx hfy hland hst s.player (by omega) (by omega)
    have hreach : Reachable r.compile.board none r.compile.initial s :=
      (Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hpre).trans hst
    exact (hreach.valid r.compile.initial_valid).2.2 hbox

/-- A complete real push consuming a source hole must approach it from below. -/
theorem landing_source_push_north {s : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hst : Reachable r.compile.board none start s)
    (run : @Run r.outputWidth r.outputHeight r.compile.board d s n)
    (hq : run.cell ⟨n + 1, by omega⟩ ∈ source r.width r.height s) : d = .north := by
  have hs := r.landing_player_below_source hpre hsf hfx hfy hland hst
  have hy := (Finset.mem_filter.mp hq).2.2
  have hpos := run.position ⟨n + 1, by omega⟩
  have hlane := run.lane ⟨n + 1, by omega⟩
  cases d <;> simp only [Direction.position, Direction.lane] at hpos hlane <;> first | rfl | omega

/-- The consumed source hole is precisely its column's southernmost current hole. -/
theorem landing_source_push_pop
    {s t : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hst : Reachable r.compile.board none start s) (hv : s.Valid r.compile.board) (hn : 0 < n)
    (run : @Run r.outputWidth r.outputHeight r.compile.board d s n)
    (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (hq : run.cell ⟨n + 1, by omega⟩ ∈ source r.width r.height s) :
    d = .north ∧ ∃ pop : BottomPop (source r.width r.height s) (source r.width r.height t),
      pop.cell = run.cell ⟨n + 1, by omega⟩ := by
  have hstep : Step r.compile.board none s t := ⟨d, .push hv hn trivial run hp hb⟩
  have hout := r.landing_no_return hpre hsf hfx hfy hland (hst.tail hstep)
  have hdir := r.landing_source_push_north hpre hsf hfx hfy hland hst run hq
  refine ⟨hdir, ?_⟩
  subst d
  exact ⟨⟨run.cell ⟨n + 1, by omega⟩, hq,
    fun p hp hx => r.north_run_maximal run
      (r.landing_player_below_source hpre hsf hfx hfy hland hst) hp hx,
    source_push run hn hp hb hout⟩, rfl⟩

/-- Every true post-commit step leaves the source unchanged or executes one unit bottom read. -/
theorem landing_step_source_read
    {s t : State r.outputWidth r.outputHeight}
    (hst : Reachable r.compile.board none start s) (hm : Step r.compile.board none s t) :
    source r.width r.height t = source r.width r.height s ∨
      ∃ col < r.width, (Scan.Instruction.read .south col 1).eval (source r.width r.height s) =
        some (source r.width r.height t) := by
  have hm0 : @Step r.outputWidth r.outputHeight r.compile.board none s t := hm
  obtain ⟨d, hmove⟩ := hm0
  cases hmove with
  | walk _ _ _ _ hb => exact Or.inl (by simp only [source, holes, hb])
  | @push n hv hn _ run hp hb =>
    have hout := r.landing_no_return hpre hsf hfx hfy hland (hst.tail hm)
    have he := source_push run hn hp hb hout
    by_cases hq : run.cell ⟨n + 1, by omega⟩ ∈ source r.width r.height s
    · obtain ⟨_, pop, hpop⟩ := r.landing_source_push_pop hpre hsf hfx hfy hland hst hv hn run hp hb hq
      refine Or.inr ⟨pop.cell.1.val, ?_, pop.read⟩
      have hh := (Finset.mem_filter.mp pop.present).2.1
      exact hh
    · exact Or.inl (he.trans (Finset.erase_eq_of_notMem hq))

end Committed
end PushPuzzle.Push.ColumnScan.Input

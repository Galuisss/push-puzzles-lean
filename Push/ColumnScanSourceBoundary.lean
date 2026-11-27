/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSeal
public import Push.ColumnScanDoor

/-! Successful pre-needle computation retains every complete source push inside its original rectangle. -/

@[expose] public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- The real player is in the original source rectangle. -/
def SourceInside (s : State r.outputWidth r.outputHeight) : Prop :=
  s.player.1.val < r.width ∧ s.player.2.val < r.height

private theorem full_source_side {s : State r.outputWidth r.outputHeight}
    (hr : Reachable r.compile.board none r.compile.initial s) (hdoor : r.door ∈ s.boxes)
    (q : Cell r.outputWidth r.outputHeight) (hx : r.width ≤ q.1.val)
    (hy : q.2.val < r.height) : q ∈ s.boxes := by
  by_cases hx' : r.width < q.1.val
  · exact r.east_full hr q hx' hy
  · by_cases hy' : q.2.val + 1 < r.height
    · exact r.northeast_full hr q hx hy'
    · have he : q = r.door := by
        apply Prod.ext <;> apply Fin.ext
        · dsimp [door]
          omega
        · dsimp [door]
          have := r.height_pos
          omega
      exact he ▸ hdoor

private theorem inside_next_north {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hs : r.SourceInside s) (ha : Adjacent d s.player t.player) :
    t.player.2.val ≤ r.height ∧ North r.width r.targetLevel t := by
  have hy : t.player.2.val ≤ r.height := by
    have hsy := hs.2
    cases d <;> simp only [Adjacent] at ha <;> omega
  refine ⟨hy, fun _ => ?_⟩
  have := r.targetLevel_lower
  omega

private theorem adjacent_below_source {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hs : r.SourceInside s) (ha : Adjacent d s.player t.player) (hy : r.height ≤ t.player.2.val) :
    t.player.1.val < r.width := by
  have hsx := hs.1
  have hsy := hs.2
  cases d <;> simp only [Adjacent] at ha <;> omega

/-- A player remaining in the source cannot have filled its only door on a successful prefix. -/
private theorem before_south_source_door_empty
    {s finish : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) : r.door ∈ holes s := by
  by_contra hhole
  have hdoor : r.door ∈ s.boxes := by simpa only [mem_holes, not_not] using hhole
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr
  have hf : ¬r.SourceInside finish := by
    intro hf
    have := r.targetLevel_lower
    have := hf.2
    omega
  obtain ⟨u, v, hsu, hu, hm, hv, hvf⟩ := Path.first_exit hsf hs hf
  have hrow : r.height ≤ r.targetLevel := by have := r.targetLevel_lower; omega
  have hsuN : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel) s u :=
    Relation.ReflTransGen.mono (fun _ _ hm =>
      ⟨hm.1, fun _ => hm.2.2.trans_le hrow⟩) _ _ hsu
  have hpre := hr.trans hsuN
  have hpreReach : Reachable r.compile.board none r.compile.initial u :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hpre
  have hreachV := hpreReach.tail hm
  have hdoorV := r.reachable_door_full hreach
    ((Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hsu).tail hm) hdoor
  have ha := players_adjacent hm.choose_spec
  obtain ⟨hyV, hNV⟩ := r.inside_next_north hu ha
  by_cases hy : v.player.2.val < r.height
  · have hx : r.width ≤ v.player.1.val := by
      by_contra hn
      exact hv ⟨by omega, hy⟩
    exact hm.valid_target.2.2 (r.full_source_side hreachV hdoorV v.player hx hy)
  · have hx : v.player.1.val < r.width := r.adjacent_below_source hu ha (by omega)
    have hh := player_mem_holes hm.valid_target
    obtain ⟨i, hi⟩ := (r.before_south_exact (hpre.tail ⟨hm, hNV⟩) hvf hfx hfy hx (by omega)).mp hh
    have hf := r.needle_far_south i
    have he := congrArg (fun q => q.2.val) hi
    omega

/-- A real successful source push reaches its first hole before leaving the source rectangle. -/
theorem before_south_push_endpoint
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hv : s.Valid r.compile.board) (hn : 0 < n)
    (run : Run r.compile.board d s n) (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) :
    (run.cell ⟨n + 1, by omega⟩).1.val < r.width ∧
      (run.cell ⟨n + 1, by omega⟩).2.val < r.height := by
  have hmove : Move r.compile.board none d s t := .push hv hn trivial run hp hb
  have hstep : Step r.compile.board none s t := ⟨d, hmove⟩
  have hsf := (Relation.ReflTransGen.single hstep).trans htf
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hr
  have hpos := run.position ⟨n + 1, by omega⟩
  have hlane := run.lane ⟨n + 1, by omega⟩
  have hfirst := run.position 1
  have hfirstlane := run.lane 1
  rw [← hp] at hfirst hfirstlane
  have hsx := hs.1
  have hsy := hs.2
  have hN := (r.inside_next_north hs (players_adjacent hmove)).2
  cases d with
  | north => simp only [Direction.position, Direction.lane] at hpos hlane; omega
  | west => simp only [Direction.position, Direction.lane] at hpos hlane; omega
  | south =>
    simp only [Direction.position, Direction.lane] at hpos hlane
    refine ⟨by omega, ?_⟩
    by_contra hy
    obtain ⟨i, hi⟩ := (r.before_south_exact hr hsf hfx hfy (by omega) (by omega)).mp
      ((mem_holes _).mpr run.empty)
    have hneedle := r.before_south_all_needles (hr.tail ⟨hstep, hN⟩) htf hfx hfy i
    have hbox : run.cell ⟨n + 1, by omega⟩ ∈ t.boxes := by
      rw [hb]
      exact Finset.mem_insert_self _ _
    exact (mem_holes _).mp hneedle (hi.symm ▸ hbox)
  | east =>
    simp only [Direction.position, Direction.lane, Fin.val_one] at hpos hlane hfirst hfirstlane
    refine ⟨?_, by omega⟩
    by_contra hx
    by_cases hx' : r.width < (run.cell ⟨n + 1, by omega⟩).1.val
    · exact run.empty (r.east_full hreach _ hx' (by omega))
    · by_cases hy' : (run.cell ⟨n + 1, by omega⟩).2.val + 1 < r.height
      · exact run.empty (r.northeast_full hreach _ (by omega) hy')
      · have he : run.cell ⟨n + 1, by omega⟩ = r.door := by
          apply Prod.ext <;> apply Fin.ext
          · dsimp [door]
            omega
          · dsimp [door]
            have := r.height_pos
            omega
        have htSource : r.SourceInside t := ⟨by omega, by omega⟩
        have hd := r.before_south_source_door_empty (hr.tail ⟨hstep, hN⟩) htf hfx hfy htSource
        exact (mem_holes _).mp hd (by rw [hb, he]; exact Finset.mem_insert_self _ _)

/-- Every cell of the actual full run is available in the original source rectangle. -/
theorem before_south_push_run_inside
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction} {n : ℕ}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hv : s.Valid r.compile.board) (hn : 0 < n)
    (run : Run r.compile.board d s n) (hp : t.player = run.cell 1)
    (hb : t.boxes = insert (run.cell ⟨n + 1, by omega⟩) (s.boxes.erase (run.cell 1)))
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hs : r.SourceInside s) (i : Fin (n + 2)) :
    (run.cell i).1.val < r.width ∧ (run.cell i).2.val < r.height := by
  obtain ⟨hex, hey⟩ := r.before_south_push_endpoint hr hv hn run hp hb htf hfx hfy hs
  have hsx := hs.1
  have hsy := hs.2
  have hpos := run.position i
  have hlane := run.lane i
  have hend := run.position ⟨n + 1, by omega⟩
  have hi := i.isLt
  cases d <;> simp only [Direction.position, Direction.lane] at hpos hlane hend <;> omega

end PushPuzzle.Push.ColumnScan.Input

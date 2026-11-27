/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanFrontier

/-! A strip's first southern entrance is westward and uses an original needle. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- First entry to a southern strip must cross its eastern boundary, one column westward. -/
theorem first_south_direction {cut : ℕ} (hcut : cut ≤ r.width)
    {s t : State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState s) (hm : Move r.compile.board none d s t)
    (hx : t.player.1.val < cut) (hy : r.targetLevel ≤ t.player.2.val) :
    d = .west ∧ s.player.1.val = cut ∧ t.player.1.val + 1 = cut := by
  apply enter_west hm (r.north_prefix_split hcut hr)
    (reachable_north hr (r.initial_north cut)) _ hx hy
  have hmax := Nat.le_max_right r.sourceHoles r.width
  have hlow := r.targetLevel_lower
  have hpos := r.height_pos
  omega

/-- Walking into the strip uses its own needle; pushing in consumes a strictly more western one. -/
theorem first_south_needle {cut : ℕ} (hcut : cut ≤ r.width)
    {s t : State r.outputWidth r.outputHeight}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none cut r.targetLevel)
      r.initialState.toState s) (hm : Step r.compile.board none s t)
    (hx : t.player.1.val < cut) (hy : r.targetLevel ≤ t.player.2.val) :
    (∃ i : Fin r.width, i.val + 1 = cut ∧ r.needle i = t.player ∧ t.boxes = s.boxes) ∨
      ∃ i : Fin r.width, i.val + 1 < cut ∧ r.needle i ∈ holes s ∧ r.needle i ∉ holes t := by
  obtain ⟨d, hm⟩ := hm
  obtain ⟨rfl, hsx, htx⟩ := r.first_south_direction hcut hr hm hx hy
  have hsub := south_subset hr
  cases hm with
  | walk hv ha hf he hb =>
    have hh : t.player ∈ south cut r.targetLevel r.initialState.toState :=
      hsub (Finset.mem_filter.mpr ⟨(mem_holes _).mpr he, hx, hy⟩)
    obtain ⟨i, hi, hp⟩ := (r.mem_south_initial hcut t.player).mp hh
    refine Or.inl ⟨i, ?_, hp, hb⟩
    have := congrArg (fun p => p.1.val) hp
    change i.val = t.player.1.val at this
    omega
  | @push n hv hn _ run hp hb =>
    let z : Cell r.outputWidth r.outputHeight := run.cell ⟨n + 1, by omega⟩
    have hzpos := run.position ⟨n + 1, by omega⟩
    have hzlane := run.lane ⟨n + 1, by omega⟩
    have hfirst := run.position 1
    rw [← hp] at hfirst
    simp only [Direction.position, Direction.lane, Fin.val_one] at hzpos hzlane hfirst
    have hzleft : z.1.val < t.player.1.val := by dsimp [z]; omega
    have hzy : z.2.val = t.player.2.val := by
      have hl := run.lane 1
      rw [← hp] at hl
      exact hzlane.trans hl.symm
    have hh : z ∈ south cut r.targetLevel r.initialState.toState :=
      hsub (Finset.mem_filter.mpr ⟨(mem_holes _).mpr run.empty, by omega, by omega⟩)
    obtain ⟨i, hi, hz⟩ := (r.mem_south_initial hcut z).mp hh
    refine Or.inr ⟨i, ?_, ?_, ?_⟩
    · have := congrArg (fun p => p.1.val) hz
      change i.val = z.1.val at this
      omega
    · rw [hz]
      exact (mem_holes _).mpr run.empty
    · rw [hz, mem_holes]
      intro hh
      exact hh (by rw [hb]; exact Finset.mem_insert_self _ _)

end PushPuzzle.Push.ColumnScan.Input

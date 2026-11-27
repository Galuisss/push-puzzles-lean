/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanNeedles

/-! Before the next needle visit, a source-avoiding reader cannot create a horizontal hole in the current column. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier

variable (r : ColumnScan.Input)

/-- Original western needles exclude both directions of horizontal hole creation in the column being read. -/
theorem before_next_move_guard (i : Fin r.width)
    {s t finish : State r.outputWidth r.outputHeight} {d : Direction}
    (hr : Relation.ReflTransGen (NorthStep r.compile.board none i.val r.targetLevel)
      r.initialState.toState s) (hm : Move r.compile.board none d s t)
    (htOutside : t.player.1.val < r.width → r.height ≤ t.player.2.val)
    (htf : Reachable r.compile.board none t finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val) :
    d = .east ∨ d = .west → s.boxes ≠ t.boxes → t.player.1.val ≠ i.val := by
  intro hd hchanged htx
  have htNorth : North i.val r.targetLevel t := fun hx => by omega
  have htY := htOutside (by omega)
  have hsf := (Relation.ReflTransGen.single (show Step r.compile.board none s t from ⟨d, hm⟩)).trans htf
  have hN := reachable_north hr (r.initial_north i.val)
  have hcut : i.val ≤ r.width := by have := i.isLt; omega
  cases hm with
  | walk _ _ _ _ hb => exact hchanged hb.symm
  | @push n hv hn hc run hp hb =>
    let q : Cell r.outputWidth r.outputHeight := run.cell ⟨n + 1, by omega⟩
    have ha := players_adjacent (Move.push hv hn hc run hp hb)
    have hpos := run.position ⟨n + 1, by omega⟩
    have hlane := run.lane ⟨n + 1, by omega⟩
    rcases hd with rfl | rfl
    · simp only [Adjacent, Direction.position, Direction.lane] at ha hpos hlane
      have hsx : s.player.1.val < i.val := by omega
      have hsy := congrArg Fin.val ha.2
      obtain ⟨j, hj⟩ := (r.before_south_cut_exact hcut hr hsf hfx hfy hsx (by omega)).mp
        (player_mem_holes hv)
      have hyj := congrArg (fun q => q.2.val) hj
      have hjlevel := r.targetLevel_le_needleLevel j
      have := hN hsx
      change r.needleLevel j = s.player.2.val at hyj
      omega
    · simp only [Adjacent, Direction.position, Direction.lane] at ha hpos hlane
      have hsy := congrArg Fin.val ha.2
      have hqx : q.1.val < i.val := by dsimp [q]; omega
      have hqy : r.height ≤ q.2.val := by dsimp [q]; omega
      obtain ⟨j, hj⟩ := (r.before_south_cut_exact hcut hr hsf hfx hfy hqx hqy).mp
        ((mem_holes _).mpr run.empty)
      have hstep : Step r.compile.board none s t := ⟨.west, Move.push hv hn hc run hp hb⟩
      have hpin := (r.before_south_cut_exact hcut (hr.tail ⟨hstep, htNorth⟩)
        htf hfx hfy hqx hqy).mpr ⟨j, hj⟩
      exact (mem_holes _).mp hpin (by rw [hb]; exact Finset.mem_insert_self _ _)

end PushPuzzle.Push.ColumnScan.Input

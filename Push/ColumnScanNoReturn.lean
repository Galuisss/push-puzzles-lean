/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanSeal
public import Push.ColumnScanSource
public import Push.ColumnScanDoor
public import Push.ReflectedFrontier

/-! A sealed reader cannot refresh enough northern rows to reenter the live source. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier ReflectedFrontier

variable (r : ColumnScan.Input)

/-- The sealed landing's real buffer gap and source hole budget exclude every later source visit. -/
theorem landing_no_return {s finish t : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState s) (hsf : Reachable r.compile.board none s finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hland : s.player = r.landing)
    (hst : Reachable r.compile.board none s t) :
    t.player.1.val < r.width → r.height ≤ t.player.2.val := by
  have hreach : Reachable r.compile.board none r.compile.initial s :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ hpre
  have hdoor := r.landing_door_occupied hpre hsf hfx hfy hland
  have hheight : r.height ≤ r.outputHeight := by dsimp [outputHeight]; omega
  have hlevel : r.targetLevel < r.outputHeight :=
    (r.targetLevel_le_needleLevel ⟨0, r.width_pos⟩).trans_lt (r.needleLevel_lt_height _)
  apply no_source_return (w := r.outputWidth) (h := r.outputHeight)
    hheight hlevel (Reachable.valid hreach r.compile.initial_valid) _ _ _ _ hst
  · intro q hq hx
    by_cases hy : q.2.val < r.height
    · exact Or.inl hy
    · right
      obtain ⟨i, hi⟩ := (r.before_south_exact hpre hsf hfx hfy hx (by omega)).mp hq
      have hqlev := r.targetLevel_le_needleLevel i
      have := congrArg (fun q => q.2.val) hi
      change r.needleLevel i = q.2.val at this
      omega
  · intro hx
    have := congrArg (fun q => q.1.val) hland
    change s.player.1.val = r.width at this
    omega
  · rw [r.before_south_source_count hpre hsf hfx hfy]
    exact (Nat.add_le_add_left (Nat.le_max_left r.sourceHoles r.width) _).trans_lt r.targetLevel_lower
  · intro u hu q hx hy
    by_cases hyn : q.2.val + 1 < r.height
    · exact r.northeast_full (hreach.trans hu) q (by omega) hyn
    · have heq : q = r.door := by
        apply Prod.ext <;> apply Fin.ext
        · exact hx
        · change q.2.val = r.height - 1
          omega
      exact heq ▸ r.reachable_door_full hreach hu hdoor

end PushPuzzle.Push.ColumnScan.Input

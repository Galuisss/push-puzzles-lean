/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicStaticSuffix
public import Push.CyclicOriginalHoles
public import Mathlib.Data.List.GetD

/-! A complete dock computation peels one exact scan round, preserving its entire future suffix. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Every accepted suffix after the real commitment lifts to the exact first column quotas. -/
theorem Commit.lift_source_suffix {r : ColumnScan.Input}
    {finish : State (dock r).outputWidth (dock r).outputHeight} (c : Commit r finish)
    {tail : List (Scan.Instruction r.width r.height)}
    (htail : Scan.Accepts tail (originalHoles r finish)) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++ tail) (holes c.sourceState) := by
  apply Scan.columns_suffix_lifts (Scan.ofQuotas_nodup r.quotas)
    (c.original_remainder c.suffix) _ _ htail
  · intro x
    let i : Fin r.quotas.length := ⟨x.val, r.quotas_width.symm ▸ x.isLt⟩
    exact ⟨r.quotas[i], Scan.ofQuotas_mem r.quotas i⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    let j : Fin r.width := ⟨i.val, r.quotas_width ▸ i.isLt⟩
    have hq := c.original_consumed_quotas j
    rw [List.getD_eq_getElem r.quotas 0 i.isLt] at hq
    simpa only [Fin.ext_iff, j, Fin.val_mk, Fin.getElem_fin, Nat.add_comm] using hq

/-- A successful physical dock observation preserves acceptance of all prescribed later source scans. -/
theorem dock_peeling_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (tail : List (Scan.Instruction r.width r.height))
    (hbound : ∀ i ∈ tail, SourceBounded r i)
    {finish : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial finish)
    (hp : finish.player = (dock r).target)
    (haccept : Scan.Accepts (unturnedProgram r rows tail) (holes finish)) :
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts
        (Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows) ++ tail)
        (holes s) := by
  obtain ⟨c⟩ := exists_commit r hr hp
  have hsource := unturned_accepts_sound r rows hlen tail hbound (holes finish)
    (c.source_row_columns c.suffix)
    (fun q hq hy => (dock_source_support r hr q hq).resolve_right (by omega)) haccept
  have hsource' : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows) ++ tail)
      (originalHoles r finish) := hsource
  refine ⟨c.sourceState, c.source_reachable, c.source_player, ?_⟩
  rw [List.append_assoc]
  exact c.lift_source_suffix hsource'

end PushPuzzle.Push.Cyclic

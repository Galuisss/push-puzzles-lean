/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicTwoRoundWitness
public import Push.ScanColumns
public import Mathlib.Data.List.GetD

/-! Exact two-round static acceptance follows from the simultaneous physical witness. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- Bottom column reads followed by west row reads on the original source rectangle. -/
def twoRoundProgram (r : ColumnScan.Input) (rows : List ℕ) : List (Scan.Instruction r.width r.height) :=
  Scan.columns (Scan.ofQuotas r.quotas) ++ Scan.lines .west (Scan.ofQuotas rows)

/-- Physical over-reading preserves acceptance of the prescribed exact two-round program. -/
private theorem TwoRoundWitness.accepts {r : ColumnScan.Input} {rows : List ℕ}
    (witness : TwoRoundWitness r rows) (hlen : rows.length = r.height) :
    Scan.Accepts (twoRoundProgram r rows) (holes witness.sourceState) := by
  have hrow : Scan.Accepts (Scan.lines .west (Scan.ofQuotas rows)) witness.residual := by
    apply Scan.lines_accepts .west _ _ (Scan.ofQuotas_nodup rows)
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    let j : Fin r.height := ⟨i.val, hlen ▸ i.isLt⟩
    have hq := witness.rowsPayable j
    have hf : witness.residual.filter (fun q => q.2 = j) =
        witness.residual.filter (fun q => Direction.west.lane q = i.val) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq, hy⟩
        exact ⟨hq, congrArg Fin.val hy⟩
      · rintro ⟨hq, hy⟩
        exact ⟨hq, Fin.ext hy⟩
    have hindex : rows.getD j.val 0 = rows[i] := by
      simpa only [Fin.getElem_fin] using List.getD_eq_getElem rows 0 i.isLt
    rwa [hf, hindex] at hq
  apply Scan.columns_suffix_lifts (Scan.ofQuotas_nodup r.quotas) witness.remainder _ _ hrow
  · intro x
    let i : Fin r.quotas.length := ⟨x.val, r.quotas_width.symm ▸ x.isLt⟩
    exact ⟨r.quotas[i], Scan.ofQuotas_mem r.quotas i⟩
  · intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    let j : Fin r.width := ⟨i.val, r.quotas_width ▸ i.isLt⟩
    have hq := witness.columnsPaid j
    rw [List.getD_eq_getElem r.quotas 0 i.isLt] at hq
    simpa only [Fin.ext_iff, j, Fin.val_mk, Fin.getElem_fin, Nat.add_comm] using hq

/-- Every solution of the actual two-stage reader yields exact two-round acceptance at one source corner. -/
theorem twoRound_sound (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    (hs : (nextInput r rows hlen hb).compile.Solvable) :
    ∃ s : State r.width r.height, Reachable r.sourceBoard none r.initial.toState s ∧
      s.player = r.sourceCorner ∧ Scan.Accepts (twoRoundProgram r rows) (holes s) := by
  obtain ⟨witness⟩ := twoRoundWitness_of_solvable r rows hlen hb hs
  exact ⟨witness.sourceState, witness.sourceReachable, witness.sourcePlayer, witness.accepts hlen⟩

end PushPuzzle.Push.Cyclic

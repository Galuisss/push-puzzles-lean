/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRoundStep
public import Push.ColumnScanCorrectness
import all Push.ColumnScanCorrectness

/-! Actual one- and two-round ordinary-reader base cases for the compact cyclic source language. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS AcceptanceProgram

/-- Paying a dense southern column vector is exactly simultaneous column inventory feasibility. -/
private theorem dense_columns_accepts_iff (r : ColumnScan.Input) (E : Finset
    (Cell r.width r.height)) :
    Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas)) E ↔
      ∀ i : Fin r.width, r.quotas.getD i.val 0 ≤ (E.filter fun q => q.1 = i).card := by
  constructor
  · rintro ⟨F, hF⟩ i
    let j : Fin r.quotas.length := ⟨i.val, by rw [r.quotas_width]; exact i.isLt⟩
    have hc := Scan.columns_card (Scan.ofQuotas_nodup _) hF (Scan.ofQuotas_mem r.quotas j)
    change (F.filter fun q => q.1.val = j.val).card + r.quotas[j] =
      (E.filter fun q => q.1.val = j.val).card at hc
    have hq : r.quotas[j] ≤ (E.filter fun q => q.1.val = j.val).card := by omega
    simpa only [j, Fin.ext_iff, List.getD_eq_getElem _ _ j.isLt, Fin.getElem_fin] using hq
  · intro hquotas
    apply Scan.columns_accepts _ _ (Scan.ofQuotas_nodup _)
    intro a ha
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp ha
    let j : Fin r.width := ⟨i.val, by rw [← r.quotas_width]; exact i.isLt⟩
    have hq := hquotas j
    simpa only [j, Fin.ext_iff, List.getD_eq_getElem _ _ i.isLt, Fin.getElem_fin] using hq

/-- The original corner-quota source language is precisely the compact language with no future block. -/
private theorem cornerQuotas_iff_language_nil
    (r : ColumnScan.Input) : r ∈ ColumnScan.cornerQuotas ↔ Language r [] := by
  constructor
  · rintro ⟨s, hr, hp, hq⟩
    refine ⟨s, hr, hp, ?_⟩
    change Scan.Accepts (Scan.columns (Scan.ofQuotas r.quotas) ++ []) (holes s)
    rw [List.append_nil]
    exact (dense_columns_accepts_iff r _).mpr hq
  · rintro ⟨s, hr, hp, ha⟩
    refine ⟨s, hr, hp, ?_⟩
    apply (dense_columns_accepts_iff r _).mp
    simpa only [instructions, List.flatMap_nil, List.append_nil] using ha

/-- The literal single reader solves exactly the current south-read source language. -/
theorem compile_solvable_iff_language_nil (r : ColumnScan.Input) : r.compile.Solvable ↔ Language r [] :=
  r.compile_solvable_iff_cornerQuotas.trans (cornerQuotas_iff_language_nil r)

/-- The actual next reader solves exactly one additional bounded sparse west-read block. -/
theorem twoRound_solvable_iff_language_west (r : ColumnScan.Input) (requests : List (ℕ × ℕ))
    (hreq : ∀ a ∈ requests, a.1 < r.height)
    (hb : (rowQuotas r requests).sum ≤ r.sourceHoles) :
    (nextInput r (rowQuotas r requests) (rowQuotas_length r requests) hb).compile.Solvable ↔
      Language r [.read .west requests] := by
  rw [compile_solvable_iff_language_nil]
  exact round_step_language_iff r requests hreq [] (by simp [instructions]) hb

end PushPuzzle.Push.Cyclic

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicRoundStep

/-! Actual next-source inventory preserves total program budgets and supplies every later erase precondition. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS AcceptanceProgram

private theorem nextQuotas_sum (r : ColumnScan.Input) (rows : List ℕ) :
    (nextQuotas r rows).sum = rows.sum +
      (r.width + 2) * ((wideReader r).outputHeight - r.height) := by
  simp only [nextQuotas, List.sum_append, List.sum_replicate, smul_eq_mul, Nat.zero_mul,
    Nat.add_zero, Nat.mul_comm]

/-- One ordinary peel preserves the complete remaining positive payment budget. -/
theorem round_step_budget (r : ColumnScan.Input) (requests : List (ℕ × ℕ))
    (hreq : ∀ a ∈ requests, a.1 < r.height) (rest : List Round)
    (hb : Budget r (.read .west requests :: rest)) :
    Budget (nextInput r (rowQuotas r requests) (rowQuotas_length r requests)
      (rowQuotas_budget r requests rest hreq hb)) (nextRounds r rest) := by
  let rows := rowQuotas r requests
  let r' := nextInput r rows (rowQuotas_length r requests) (rowQuotas_budget r requests rest hreq hb)
  have hfuture : rows.sum + Scan.quota (instructions (w := r.width) (h := r.height) rest) ≤
      r.sourceHoles := by
    change r.quotas.sum + Scan.quota
      (Scan.lines .west requests ++ instructions (w := r.width) (h := r.height) rest) ≤ r.sourceHoles at hb
    rw [Scan.quota_append, Scan.lines_quota] at hb
    have hs := Scan.denseQuotas_sum .west r.width r.height requests hreq
    change (Scan.denseQuotas .west r.width r.height requests).sum + _ ≤ _
    rw [hs]
    omega
  have hsum : r'.quotas.sum = rows.sum +
      (r.width + 2) * ((wideReader r).outputHeight - r.height) := nextQuotas_sum r rows
  have htail : Scan.quota (instructions (w := r'.width) (h := r'.height) (nextRounds r rest)) =
      Scan.quota (instructions (w := r.width) (h := r.height) rest) := nextRounds_quota r rest
  have hinv := initial_inventory_lower r
  change r'.quotas.sum + Scan.quota (instructions (w := r'.width) (h := r'.height) (nextRounds r rest)) ≤
    (holes (nextSource r).initial).card
  rw [hsum, htail]
  omega

/-- The newly charged auxiliary rows already pay at least one full next-source height. -/
theorem nextInput_height_le_quota (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    (hextra : r.extraWidth ≤ r.width) :
    (nextInput r rows hlen hb).height ≤ (nextInput r rows hlen hb).quota := by
  have hL : 7 ≤ (wideReader r).outputHeight - r.height := by
    have hl := r.length_ge_seven
    change 7 ≤ r.height + r.length - r.height
    omega
  have hmul := Nat.mul_le_mul_left (r.width + 2) hL
  have hsum := nextQuotas_sum r rows
  change r.width + 2 + (r.width + 1 + r.extraWidth) + 2 ≤ (nextQuotas r rows).sum
  rw [hsum]
  omega

end PushPuzzle.Push.Cyclic

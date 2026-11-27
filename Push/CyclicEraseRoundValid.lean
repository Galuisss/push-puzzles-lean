/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicEraseRoundStep
public import Push.CyclicEraseInventoryProgram
import all Push.CyclicErasePeelingCorrectness
import all Push.CyclicEraseRounds

/-! The literal compact erase replacement preserves actual lane bounds and the complete positive quota budget. -/

public section
namespace PushPuzzle.Push.CyclicErase

open PushFS PushS AcceptanceProgram

/-- Every literal suffix block of the erase expansion names an actual lane of the turned source. -/
private theorem suffixRounds_bounded (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height)
    (selected : Finset (Fin r.width)) (tail : List Round)
    (hbound : ∀ i ∈ instructions tail, Cyclic.SourceBounded r i) :
    Scan.Bounded (instructions (w := (eraseDock r).outputHeight) (h := (eraseDock r).outputWidth)
      (suffixRounds r selected tail)) := by
  have hb := Cyclic.turnProgram_bounded _ (unturned_bounded r rows hlen selected (instructions tail) (by
    intro i hi
    apply (Cyclic.sourceBounded_iff_bounded (asReader r) i).mpr
    exact (Cyclic.sourceBounded_iff_bounded r i).mp (hbound i hi)))
  change Scan.Bounded (peeledProgram r rows selected (instructions tail)) at hb
  rw [transformed_instructions] at hb
  intro i hi
  exact hb i (List.mem_append_right _ hi)

/-- The same actual lane bounds hold in the new factory-created reader's source coordinates. -/
theorem suffixRounds_sourceBounded (r : ColumnScan.Input) (rows : List ℕ) (hlen : rows.length = r.height)
    (hrows : rows.sum ≤ r.sourceHoles) (selected : Finset (Fin r.width)) (tail : List Round)
    (hbound : ∀ i ∈ instructions tail, Cyclic.SourceBounded r i) :
    ∀ i ∈ instructions (w := (nextInput r rows hlen hrows).width) (h := (nextInput r rows hlen hrows).height)
      (suffixRounds r selected tail), Cyclic.SourceBounded (nextInput r rows hlen hrows) i := by
  intro i hi
  apply (Cyclic.sourceBounded_iff_bounded _ i).mpr
  exact suffixRounds_bounded r rows hlen selected tail hbound i hi

private theorem future_budget (r : ColumnScan.Input) (requests : List (ℕ × ℕ))
    (hreq : ∀ a ∈ requests, a.1 < r.height) (lanes : Finset ℕ) (rest : List Round)
    (hb : Cyclic.Budget r (.read .west requests :: .clear .north lanes :: rest)) :
    (Cyclic.rowQuotas r requests).sum + Scan.quota (instructions (w := r.width) (h := r.height) rest) ≤
      r.sourceHoles := by
  change r.quotas.sum + Scan.quota (Scan.lines .west requests ++
    ([.clear .north lanes] ++ instructions (w := r.width) (h := r.height) rest)) ≤ r.sourceHoles at hb
  have hz : Scan.quota (w := r.width) (h := r.height) [.clear .north lanes] = 0 := rfl
  rw [Scan.quota_append, Scan.quota_append, Scan.lines_quota, hz] at hb
  have hs := Scan.denseQuotas_sum .west r.width r.height requests hreq
  change (Scan.denseQuotas .west r.width r.height requests).sum + _ ≤ _
  rw [hs]
  omega

/-- Erase replacement preserves the complete positive payment budget on the actual next live source. -/
theorem round_step_budget (r : ColumnScan.Input) (hk : r.height ≤ r.quota)
    (requests : List (ℕ × ℕ)) (hreq : ∀ a ∈ requests, a.1 < r.height)
    (lanes : Finset ℕ) (rest : List Round)
    (hb : Cyclic.Budget r (.read .west requests :: .clear .north lanes :: rest)) :
    Cyclic.Budget (nextInput r (Cyclic.rowQuotas r requests) (Cyclic.rowQuotas_length r requests)
      (Cyclic.rowQuotas_budget r requests (.clear .north lanes :: rest) hreq hb))
      (suffixRounds r (selectColumns r lanes) rest) := by
  let rows := Cyclic.rowQuotas r requests
  change (firstQuotas r rows).sum + Scan.quota
    (instructions (w := (eraseDock r).outputHeight) (h := (eraseDock r).outputWidth)
      (suffixRounds r (selectColumns r lanes) rest)) ≤ (holes (nextSource r).initial).card
  rw [suffixRounds_quota]
  exact turnedProgram_budget r hk rows (selectColumns r lanes) (instructions rest)
    (future_budget r requests hreq lanes rest hb)

end PushPuzzle.Push.CyclicErase

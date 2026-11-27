/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicObservation
public import Push.ColumnScanCorrectness

/-! Simultaneous two-round evidence from one real source computation and its ordered residual. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS ReaderResidual

/-- One original source corner state, its bottom-read residual, and the next row quotas. -/
structure TwoRoundWitness (r : ColumnScan.Input) (rows : List ℕ) where
  sourceState : State r.width r.height
  sourceReachable : Reachable r.sourceBoard none r.initial.toState sourceState
  sourcePlayer : sourceState.player = r.sourceCorner
  residual : Finset (Cell r.width r.height)
  remainder : BottomRemainder (holes sourceState) residual
  columnsPaid : ∀ i : Fin r.width, r.quotas.getD i.val 0 +
    (residual.filter fun q => q.1 = i).card ≤ ((holes sourceState).filter fun q => q.1 = i).card
  rowsPayable : ∀ j : Fin r.height, rows.getD j.val 0 ≤ (residual.filter fun q => q.2 = j).card

/-- A complete next-reader corner observation yields two rounds on the same original source state. -/
private theorem twoRoundWitness (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    {t : State (nextSource r).width (nextSource r).height}
    (hr : Reachable (nextInput r rows hlen hb).sourceBoard none
      (nextInput r rows hlen hb).initial.toState t)
    (ht : t.player = (nextInput r rows hlen hb).sourceCorner)
    (hquotas : ∀ i : Fin (nextInput r rows hlen hb).width,
      (nextInput r rows hlen hb).quotas.getD i.val 0 ≤ ((holes t).filter fun q => q.1 = i).card) :
    Nonempty (TwoRoundWitness r rows) := by
  obtain ⟨obs⟩ := observe_nextInput r rows hlen hb hr ht
  obtain ⟨c⟩ := exists_commit r obs.reachable obs.player
  refine ⟨⟨c.sourceState, c.source_reachable, c.source_player, originalHoles r obs.state,
    c.original_remainder c.suffix, c.original_consumed_quotas, ?_⟩⟩
  intro j
  have hheight : r.height ≤ (nextSource r).width := by
    change r.height ≤ (wideReader r).outputHeight + (dock r).distance
    change r.height ≤ r.height + (wideReader r).length + (dock r).distance
    omega
  let i : Fin (nextInput r rows hlen hb).width := ⟨j.val, j.isLt.trans_le hheight⟩
  have hq := hquotas i
  have hindex : (nextInput r rows hlen hb).quotas.getD i.val 0 = rows.getD j.val 0 := by
    change (nextQuotas r rows).getD j.val 0 = rows.getD j.val 0
    rw [nextQuotas, List.append_assoc, List.getD_append _ _ _ _ (by rw [hlen]; exact j.isLt)]
  have hcol : rows.getD j.val 0 ≤ ((holes t).filter fun q => q.1.val = j.val).card := by
    rw [hindex] at hq
    have hf : (holes t).filter (fun q => q.1 = i) = (holes t).filter (fun q => q.1.val = j.val) := by
      ext q
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hq, hx⟩
        exact ⟨hq, congrArg Fin.val hx⟩
      · rintro ⟨hq, hx⟩
        exact ⟨hq, Fin.ext hx⟩
    rwa [hf] at hq
  have hactual : rows.getD j.val 0 ≤
      ((holes ((turnGeometry (dock r).outputWidth (dock r).outputHeight).state obs.state)).filter
        fun q => q.1.val = j.val).card := obs.turned.symm ▸ hcol
  have hbound := hactual.trans_eq (c.next_source_row_card j.val j.isLt)
  simpa only [Fin.ext_iff] using hbound

/-- A successful actual two-stage reader yields its simultaneous original two-round source evidence. -/
theorem twoRoundWitness_of_solvable (r : ColumnScan.Input) (rows : List ℕ)
    (hlen : rows.length = r.height) (hb : rows.sum ≤ r.sourceHoles)
    (hs : (nextInput r rows hlen hb).compile.Solvable) : Nonempty (TwoRoundWitness r rows) := by
  obtain ⟨t, hr, ht, hq⟩ := (nextInput r rows hlen hb).compile_solvable_implies_corner_quotas hs
  exact twoRoundWitness r rows hlen hb hr ht hq

end PushPuzzle.Push.Cyclic

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.CyclicCommitGeometry
public import Push.ReaderResidual
public import Push.ReaderSourcePop

/-! The same committed source bitmap pays the first quotas throughout the complete physical dock suffix. -/

public section
namespace PushPuzzle.Push.Cyclic.Commit

open PushFS PushS ReflectedFrontier

variable {r : ColumnScan.Input} {finish : State (dock r).outputWidth (dock r).outputHeight}
  (c : Commit r finish)

/-- Every post-commit player stays below the original source rows, throughout the entire dock. -/
theorem below_source {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t) : r.height ≤ t.player.2.val := by
  by_contra hy
  by_cases hx : t.player.1.val < r.width + 2
  · have := c.no_return hr hx
    omega
  · have hbox := c.right_full hr t.player (by omega) (by omega)
    exact (Reachable.valid (c.before_real.trans hr) (dock r).compile.initial_valid).2.2 hbox

/-- No later part of the physical dock run can add a source hole. -/
theorem source_between_subset {s t : State (dock r).outputWidth (dock r).outputHeight}
    (hcs : Reachable (dock r).compile.board none c.state s)
    (hst : Reachable (dock r).compile.board none s t) :
    source (r.width + 2) r.height t ⊆ source (r.width + 2) r.height s := by
  apply ReaderResidual.reachable_source_subset
  apply Path.enrich hst
  intro a b hsa hm hbt
  exact ⟨hm, c.no_return ((hcs.trans hsa).tail hm)⟩

private theorem source_column_between_subset (i : Fin r.width)
    {s t : State (dock r).outputWidth (dock r).outputHeight}
    (hcs : Reachable (dock r).compile.board none c.state s)
    (hst : Reachable (dock r).compile.board none s t) : sourceColumn r i t ⊆ sourceColumn r i s := by
  intro q hq
  obtain ⟨hq, hx, hy⟩ := Finset.mem_filter.mp hq
  have hs := c.source_between_subset hcs hst (Finset.mem_filter.mpr
    ⟨hq, by rw [hx]; have := i.isLt; omega, hy⟩)
  exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hs).1, hx, hy⟩

/-- The final dock bitmap has consumed all first-round quotas from that same source. -/
theorem consumed_quotas : ∀ i : Fin r.width,
    r.quotas.getD i.val 0 + (sourceColumn r i finish).card ≤ (sourceColumn r i c.state).card := by
  intro i
  have hbefore : Reachable (dock r).compile.board none c.state c.readerEnd :=
    Relation.ReflTransGen.mono (fun _ _ hm => hm.1) _ _ c.untilGoal
  have hc := Finset.card_le_card (c.source_column_between_subset i hbefore c.afterGoal)
  have hb := c.reader_consumed_quotas i
  omega

/-- On source rows, every post-commit hole is an actual original source cell. -/
theorem source_row_columns {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t)
    (q : Cell (dock r).outputWidth (dock r).outputHeight) (hq : q ∈ holes t)
    (hy : q.2.val < r.height) : 2 ≤ q.1.val ∧ q.1.val < r.width + 2 := by
  have hwhole := c.before_real.trans hr
  have hlow : r.height + max r.sourceHoles r.width < (wideReader r).targetLevel := r.targetLevel_lower
  constructor
  · by_contra hx
    have hbox := dock_northwest_full r hwhole q (by omega) (by omega)
    exact (mem_holes _).mp hq hbox
  · by_contra hx
    exact (mem_holes _).mp hq (c.right_full hr q (by omega) hy)

/-- Complete physical consumption retains northern prefixes in all original source columns. -/
theorem source_remainder {t : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none c.state t) :
    ReaderResidual.BottomRemainder (source (r.width + 2) r.height c.state)
      (source (r.width + 2) r.height t) := by
  apply ReaderResidual.source_remainder
  apply Path.enrich hr
  intro a b hca hm hbt
  exact ⟨hm, c.below_source hca, c.below_source (hca.tail hm)⟩

end PushPuzzle.Push.Cyclic.Commit

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import PushPush.ColumnReaderForward
import all PushPush.ColumnReaderForward
import all Push.ColumnScanForwardExact
import all Push.ColumnScan

/-! The selected maximum reader preserves its eastern room and original-row support. -/

@[expose] public section
namespace PushPuzzle.PushPush.ColumnReader

open PushFS (Cell State)
open PushS Reader

variable (r : Push.ColumnScan.Input)

/-- The concrete whole-run reader retains its complete room and has no auxiliary
hole on an original source row. -/
theorem compile_run_frame
    (hcorner : r.initial.player = r.sourceCorner)
    (F : Fin r.width → Finset (Cell r.outputWidth r.outputHeight))
    (H : ∀ i, ExactNorthRead (sourceColumn r i) (F i))
    (hq : ∀ i, r.quotas.getD i.val 0 ≤ (sourceColumn r i \ F i).card) :
    ∃ t : State r.outputWidth r.outputHeight, ReadPath r.compile.initial t ∧ t.player = r.target ∧
      (∀ i : Fin r.width, remainingColumn r t i = F i) ∧ r.room ⊆ holes t ∧
      ∀ q ∈ holes t, q.2.val < r.height → q.1.val < r.width := by
  obtain ⟨t, hr, hx, hy, hframe, hF⟩ := read_columns r F H hq r.width le_rfl r.sealedState.toState
    (Finset.notMem_compl.mpr r.sealedState.player_empty) rfl (by
      change r.firstLevel = r.firstLevel - (r.quotas.drop r.width).sum
      rw [← r.quotas_width, List.drop_length, List.sum_nil, Nat.sub_zero]) (by
      intro p hp
      simpa only [HoleState.toState, Finset.mem_compl, not_not] using r.sealedState_source_columns p hp)
  refine ⟨t, (sealed_readPath r hcorner).trans hr, Prod.ext (Fin.ext hx) (Fin.ext hy),
    fun i => hF i i.isLt, ?_, ?_⟩
  · intro q hq
    have hqx := (Finset.mem_filter.mp hq).2.1
    apply (mem_holes q).mpr
    apply (not_congr (hframe q (by omega))).mpr
    have hs : q ∈ r.sealedState.empty :=
      (r.sealedState_off_separator q (by omega)).mpr
        (Finset.mem_union_right _ (Finset.mem_union_left _ (Finset.mem_union_right _ hq)))
    simpa only [HoleState.toState, Finset.mem_compl, not_not] using hs
  · intro q hq hrow
    by_contra hwide
    have hs : q ∈ r.sealedState.empty := by
      have hqt : q ∉ t.boxes := (mem_holes q).mp hq
      have hqs := (not_congr (hframe q (by omega))).mp hqt
      simpa only [HoleState.toState, Finset.mem_compl, not_not] using hqs
    exact hwide (r.sealed_source_rows q hs hrow)

end PushPuzzle.PushPush.ColumnReader

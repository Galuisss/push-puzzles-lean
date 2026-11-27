/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.ColumnScanResidual
public import Push.ReaderResidualOrder

/-! Every actual post-commit residual is a bottom-first remainder of the same source hole set. -/

public section
namespace PushPuzzle.Push.ColumnScan.Input

open PushFS PushS StripFrontier ReflectedFrontier ReaderResidual

variable (r : ColumnScan.Input)

/-- Arbitrary physical reader behavior retains a northern prefix in each source column. -/
theorem landing_source_remainder {start finish t : State r.outputWidth r.outputHeight}
    (hpre : Relation.ReflTransGen (NorthStep r.compile.board none r.width r.targetLevel)
      r.initialState.toState start) (hsf : Reachable r.compile.board none start finish)
    (hfx : finish.player.1.val = 0) (hfy : r.targetLevel ≤ finish.player.2.val)
    (hland : start.player = r.landing) (hst : Reachable r.compile.board none start t) :
    BottomRemainder (source r.width r.height start) (source r.width r.height t) := by
  induction hst with
  | refl => exact .refl _
  | @tail s t hsu hm ih =>
    have hm0 : @Step r.outputWidth r.outputHeight r.compile.board none s t := hm
    obtain ⟨d, hmove⟩ := hm0
    cases hmove with
    | walk _ _ _ _ hb => simpa only [source, holes, hb] using ih
    | @push n hv hn _ run hp hb =>
      by_cases hq : run.cell ⟨n + 1, by omega⟩ ∈ source r.width r.height s
      · obtain ⟨_, pop, _⟩ := r.landing_source_push_pop hpre hsf hfx hfy hland hsu hv hn run hp hb hq
        exact ih.pop pop
      · have hout := r.landing_no_return hpre hsf hfx hfy hland (hsu.tail hm)
        have he := (source_push run hn hp hb hout).trans (Finset.erase_eq_of_notMem hq)
        simpa only [he] using ih

end PushPuzzle.Push.ColumnScan.Input

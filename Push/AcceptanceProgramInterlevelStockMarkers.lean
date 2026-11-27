/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockAux
public import PushS.PortGateMarkers
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortGateMarkers
import all PushS.PortWalkBudget
import all PushS.EndpointWalking

/-! Every emitted interlevel metadata entry names an actual canonical fixed target hole. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS Push.AcceptanceProgram

/-- The literal metadata row and column are a real fixed hole of every canonical endpoint word. -/
private theorem acceptancePageColumn_marker_hole (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool) (side : Side)
    {a : PageColumn} (ha : a ∈ Push.AcceptanceProgram.pageColumns l p side)
    (hj : 1 ≤ a.level) (hjm : a.level < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = a.column) (hy : q.2.val = interlevelRow p side a.level) :
    q ∈ targetHoles l p target := by
  classical
  rcases acceptance_column_data l p side ha with ⟨e, he, hside, hlevel, hcol⟩ | ⟨hside, hlevel, i, hi, hcol⟩
  · apply l.interlevelMarkers_subset_encoded p hl hM (l.canonical target) a.level
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, e, he, hlevel.symm, hlevel ▸ hjm, ?_⟩
    have hrow : q.2.val = if e.side = .upper then
        (readDepth p e.level + readDepth p (e.level + 1)) / 2
        else p.H - (readDepth p e.level + readDepth p (e.level + 1)) / 2 := by
      rw [readDepth_eq p (by omega) (by omega), readDepth_eq p (by omega) (by omega)]
      simpa only [interlevelRow, interlevelDepth, hside, hlevel] using hy
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol
    rcases hcol with hf | hr
    · exact ⟨.f, hx.trans hf, hrow⟩
    · exact ⟨.r, hx.trans hr, hrow⟩
  · apply l.gateInterlevelMarkers_subset_encoded p (l.canonical target)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, i, hi, hx ▸ hcol, ?_⟩
    · omega
    · rw [readDepth_eq p le_rfl p.levels_pos, readDepth_eq p (by omega) (by omega)]
      simpa only [interlevelRow, interlevelDepth, hside, hlevel, reduceCtorEq, ite_false] using hy

end PushPuzzle.PushS.PortLayout

namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS

/-- Every actual interlevel marker coordinate occurs in every canonical target bitmap. -/
theorem interlevelMarker_target (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (target : List Bool) (side : PortLayout.Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) : q ∈ targetHoles l p target := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  apply l.acceptancePageColumn_marker_hole p hl hM target side ha hj hjm hx
  have hb := interlevelDepth_bounds p hj hjm
  have hh : p.H = 2 * p.D := rfl
  have hq := q.2.isLt
  cases side <;> simp only [pageDepth, interlevelRow, trimDepth, ite_eq_left hjm,
    interlevelDepth, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega

end PushPuzzle.Push.AcceptanceProgram

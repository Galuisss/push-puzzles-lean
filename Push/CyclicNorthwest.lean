/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.Cyclic
public import Push.ConvexSupport

/-! The added western dock columns stay solid above the old reader's left target. -/

public section
namespace PushPuzzle.Push.Cyclic

open PushFS PushS

/-- All real trajectories keep the dock's northwest quadrant occupied. -/
theorem dock_northwest_full (r : ColumnScan.Input)
    {s : State (dock r).outputWidth (dock r).outputHeight}
    (hr : Reachable (dock r).compile.board none (dock r).compile.initial s)
    (q : Cell (dock r).outputWidth (dock r).outputHeight)
    (hx : q.1.val < 2) (hy : q.2.val < (wideReader r).targetLevel) : q ∈ s.boxes := by
  have hi : PushS.Support.Supported {p : Cell (dock r).outputWidth (dock r).outputHeight |
      2 ≤ p.1.val ∨ (wideReader r).targetLevel ≤ p.2.val} (dock r).compile.initial := by
    intro p hp
    have hh : p ∈ ((dock r).extend (dock r).initial).empty := by
      exact ((dock r).extend (dock r).initial).holes_toState ▸ (mem_holes _).mpr hp
    rcases Finset.mem_union.mp hh with hsource | haux
    · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hsource
      exact Or.inl (by change 2 ≤ a.1.val + 2; omega)
    · rcases Finset.mem_insert.mp haux with rfl | hwalk
      · exact Or.inr le_rfl
      · right
        have hwork := (Finset.mem_filter.mp hwalk).2.2
        have hlevel := (wideReader r).targetLevel_le_needleLevel ⟨0, r.width_pos⟩
        have hbound := (wideReader r).needleLevel_lt_height ⟨0, r.width_pos⟩
        change (wideReader r).outputHeight ≤ p.2.val at hwork
        omega
  have hs := (Push.Support.northwest_compl_axisConvex 2 (wideReader r).targetLevel).reachable_target hr hi
  by_contra hq
  have := hs q hq
  change 2 ≤ q.1.val ∨ (wideReader r).targetLevel ≤ q.2.val at this
  omega

end PushPuzzle.Push.Cyclic

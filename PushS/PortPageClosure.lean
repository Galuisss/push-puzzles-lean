/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortPageBackground
public import PushS.FreezePaths
import all PushS.PortWideGeometry
import all PushS.PortCentralStrip

/-! The concrete central and wide-bar closure over the actual two-page background. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS

/-- Strictly on one side of the cut, page support uses exactly that page's columns and the
selected working rows. -/
theorem page_support_iff_side (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) (q : Cell (p.W + 1) (p.H + 1))
    (hy : if side = .upper then q.2.val < p.D else p.D < q.2.val) :
    q ∈ (l.twoPageStreets p hl).support ↔ q.2 ∈ l.workingRowSet p ∨ q.1 ∈ l.pageColumnSet p side := by
  change (q.2 ∈ l.workingRowSet p ∨ q.1 ∈ l.mainColumnSet p ∨
    (q.1 ∈ l.pageColumnSet p .upper ∧ q.2.val ≤ p.D) ∨
    (q.1 ∈ l.pageColumnSet p .lower ∧ p.D ≤ q.2.val)) ↔ _
  cases side with
  | upper =>
    simp only [ite_true] at hy
    constructor
    · rintro (hr | hm | hu | hl')
      · exact Or.inl hr
      · exact Or.inr (l.mainColumnSet_subset_pageColumnSet p hl .upper hm)
      · exact Or.inr hu.1
      · exact False.elim (by omega)
    · rintro (hr | hc)
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inl ⟨hc, by omega⟩))
  | lower =>
    simp only [reduceCtorEq, ite_false] at hy
    constructor
    · rintro (hr | hm | hu | hl')
      · exact Or.inl hr
      · exact Or.inr (l.mainColumnSet_subset_pageColumnSet p hl .lower hm)
      · exact False.elim (by omega)
      · exact Or.inr hl'.1
    · rintro (hr | hc)
      · exact Or.inl hr
      · exact Or.inr (Or.inr (Or.inr ⟨hc, by omega⟩))

/-- The cut-page background, central auxiliary columns, and wide middle bars. -/
@[expose] noncomputable def pageFrozenBlockers (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) : Finset (Cell (p.W + 1) (p.H + 1)) :=
  l.pageBlockers p hl ∪ l.wideFrozenBlockers p

/-- A selected row away from its page columns has a frozen background cell immediately north. -/
theorem workingRow_north_blocker (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {v : ℕ} (hv : v ∈ l.workingDepthCoordinates p)
    (q : Cell (p.W + 1) (p.H + 1))
    (hrow : q.2.val = if side = .upper then v else p.H - v)
    (hcol : q.1 ∉ l.pageColumnSet p side) :
    ∃ r, Adjacent .north q r ∧ r ∈ l.pageFrozenBlockers p hl := by
  have hpos := workingDepth_positive l p hv
  have hvmax := workingRows_le_last l p hv
  have hD := last_depth_margin p
  have hH : p.H = 2 * p.D := rfl
  have hy : 0 < q.2.val := by
    cases hs : side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hrow <;> omega
  have heven : q.2.val % 2 = 0 := by
    apply l.workingRowSet_even p
    exact l.mem_workingRowSet_of_onSide p hv side q.2 hrow
  let r : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨q.2.val - 1, by have := q.2.isLt; omega⟩)
  refine ⟨r, ⟨rfl, by change q.2.val - 1 + 1 = q.2.val; omega⟩, ?_⟩
  have hoff : r ∉ (l.twoPageStreets p hl).support := by
    intro hp
    have hside : if side = .upper then r.2.val < p.D else p.D < r.2.val := by
      cases hs : side <;> simp only [hs, reduceCtorEq, ite_true, ite_false] at hrow ⊢ <;>
        dsimp only [r] <;> omega
    rcases (l.page_support_iff_side p hl side r hside).mp hp with hr | hc
    · have hodd := l.workingRowSet_even p hr
      change (q.2.val - 1) % 2 = 0 at hodd
      omega
    · exact hcol hc
  by_cases hc : r ∈ l.centralMarkers p
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _ hc))
  · exact Finset.mem_union_left _ (Finset.mem_union_right _
      ((l.mem_pageBackgroundBoxes p hl r).mpr ⟨hoff, hc⟩))

/-- The actual two-stage background closure remains valid over the sharper page blockers. -/
theorem pageBackground_closure (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : SignalState) :
    Freeze.Closure (l.physicalInstance p hl hM ha initial target).initial (l.pageBlockers p hl)
      (l.pageFrozenBlockers p hl) :=
  (l.wideBackground_closure p hl hM ha initial target).enlarge_blockers
    (l.wideBlockers_subset_pageBlockers p hl)

section Solution
variable (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
  (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (initial target : SignalState)

/-- Every actual solution prefix avoids the computed page and geometric freezing closure. -/
theorem physicalInstance_page_closure_avoiding {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    Relation.ReflTransGen (Freeze.AvoidingStep
      (l.physicalInstance p hl hM ha initial target).board none (l.pageFrozenBlockers p hl))
      (l.physicalInstance p hl hM ha initial target).initial u :=
  (l.pageBackground_closure p hl hM ha initial target).reachable
    (l.physicalInstance_page_avoiding_prefix p hl hM ha initial target hsu hut ht)

/-- The original physical box identities in the complete page closure stay at their initial cells. -/
theorem physicalInstance_page_closure_frozen {ι : Type} [Fintype ι]
    (S : LabelledState ι (p.W + 1) (p.H + 1))
    (hS : S.state = (l.physicalInstance p hl hM ha initial target).initial)
    {u t : State (p.W + 1) (p.H + 1)}
    (hsu : Reachable (l.physicalInstance p hl hM ha initial target).board none
      (l.physicalInstance p hl hM ha initial target).initial u)
    (hut : Reachable (l.physicalInstance p hl hM ha initial target).board none u t)
    (ht : t.boxes = (l.physicalInstance p hl hM ha initial target).board.goals) :
    ∃ U : LabelledState ι (p.W + 1) (p.H + 1), U.state = u ∧
      Labels.GuardedReachable (l.physicalInstance p hl hM ha initial target).board none
        (l.pageFrozenBlockers p hl) S U ∧
      ∀ i, S.position i ∈ l.pageFrozenBlockers p hl → U.position i = S.position i := by
  have hguard := l.physicalInstance_page_closure_avoiding p hl hM ha initial target hsu hut ht
  rw [← hS] at hguard
  obtain ⟨U, hU, hlabels⟩ := Labels.lift_guarded hguard
  exact ⟨U, hU, hlabels, hlabels.position⟩

end Solution
end PushPuzzle.PushS.PortLayout

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportLowerHead
public import Push.AcceptanceProgramInterlevelStockAux
import all Push.AcceptanceSoundnessCentral
import all Push.AcceptanceSoundnessSupportClean
import all Push.AcceptanceProgramLayout
import all PushS.PortLayoutCoordinates

/-! The real half-depth row can be paid only by the actual core and private marker columns. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

/-- The actual final working-stage clear confines every page-check residual hole to an auxiliary or gate-core column. -/
theorem canonical_page_residual_columns (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 25) : q.1.val ∈ auxiliaries l p ∪ cores l p := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hi : stages[24]? = some (.clear .north (Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p))) := by
    simp only [stages, schedule, preparation, frameSchedule, List.cons_append, List.nil_append,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  have hbefore := roundResidual_antitone stages T E hc (by omega : 24 ≤ 25) hq
  have hkeep := (roundResidual_clear_keeps stages T E 24 hc hi hbefore).2
  change q.1.val ∉ Finset.range (p.W + 1) \ (auxiliaries l p ∪ cores l p) at hkeep
  by_contra hn
  exact hkeep (Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr q.1.isLt, hn⟩)

/-- Before the actual half-depth read, all real holes on its row are in the canonical core/private stock. -/
theorem canonical_half_input_stock (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (initial target : List Bool)
    {t : State (p.W + 1) (p.H + 1)}
    (hr : Reachable (l.canonicalInstance p hl hM haxes initial target).board none
      (l.canonicalInstance p hl hM haxes initial target).initial t)
    (ha : Scan.Accepts (instructions (program l p target).rounds) (PushS.holes t))
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ roundResidual (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target) (PushS.holes t) 26) (hy : q.2.val = p.H - p.Y 1 / 2) :
    q.1.val ∈ cores l p ∪ privateColumns l p := by
  let T := targetHoles l p target
  let E := PushS.holes t
  let stages := schedule l p (T \ Boundary.frame).card
  have hc := (program_clean_execution l p hl hM haxes initial target hr
    (canonical_initial_holes l p hl hM haxes initial target) ha).2
  have hq25 := roundResidual_antitone stages T E hc (by omega : 25 ≤ 26) hq
  rcases Finset.mem_union.mp (canonical_page_residual_columns l p hl hM haxes initial target hr ha hq25) with haux | hcore
  · by_contra hout
    have hprivate : q.1.val ∉ privateColumns l p := fun h => hout (Finset.mem_union_right _ h)
    have hD := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hD
    have hH : p.H = 2 * p.D := rfl
    have hrow := q.2.isLt
    have hlive : q.1.val ∈ lowerLiveColumns l p := by
      by_contra hn
      have hb := canonical_nonlive_lower_depth_le_cut l p hl hM haxes initial target hr ha hq25 haux hn
      omega
    obtain ⟨a, hac, hax⟩ := List.mem_map.mp (List.mem_toFinset.mp hlive)
    obtain ⟨hac, hj⟩ := List.mem_filter.mp hac
    have hj : 1 ≤ a.level ∧ a.level < p.levels := of_decide_eq_true hj
    have hpublic : a.privateColumn = false := by
      cases hp : a.privateColumn
      · rfl
      · apply False.elim
        apply hprivate
        exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨a, List.mem_filter.mpr ⟨hac, hp⟩, hax⟩)
    have hbound := canonical_trim_retained_depth l p hl hM haxes initial target hr ha .lower hac hpublic 26
      (by decide) hq hax.symm
    have hmono := PortLayout.Y_le p hj.1
    have hY := p.Y_ge 1
    simp only [pageDepth, reduceCtorEq, ite_false, hy] at hbound
    omega
  · exact Finset.mem_union_left _ hcore

end PushPuzzle.Push.AcceptanceSoundness

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramTrimStockColumns
public import Push.AcceptanceSoundnessCentralStock
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramColumns
import all PushS.PortSegments

/-! Each actual whole public trim pays its canonical corridor inventory in every selected column. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- The actual frame and side clear, and the preceding lower trim on the upper page. -/
@[expose] def trimBeforeSchedule (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (side : Side) : List Template :=
  AcceptanceSoundness.sideClearSchedule l p target ++
    if side = .upper then [trimRound l p .lower] else []

private theorem pageColumn_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (side : Side) {a : PageColumn} (hac : a ∈ pageColumns l p side) :
    1 ≤ a.level ∧ a.level ≤ p.levels ∧ 0 < a.column ∧ a.column < p.W := by
  rcases acceptance_column_data l p side hac with ⟨e, he, _, hj, hx⟩ | ⟨_, hj, i, hi, hx⟩
  · obtain ⟨hj0, hjm⟩ := l.endpoints_level_bounds p hl hM he
    have hb := column_inside p ((l.endpoints_port_lt hl he).trans_le ha)
      (endpoint_columns_span p e (show a.column ∈ endpointColumns p e from by
        simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
        tauto))
    exact ⟨hj ▸ hj0, hj ▸ hjm, hb⟩
  · have hb := column_inside p (center_port l p hl ha hi)
      (center_columns_span p i (List.mem_cons_of_mem _ hx))
    exact ⟨by omega, by have := p.levels_pos; omega, hb⟩

private theorem trimDepth_lt_D (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j ≤ p.levels) : trimDepth p j < p.D := by
  unfold trimDepth
  split
  next h =>
    have h0 := readDepth_add_lt_D p j
    have h1 := readDepth_add_lt_D p (j + 1)
    rw [readDepth_eq p hj hjm] at h0
    rw [readDepth_eq p (by omega) (by omega)] at h1
    omega
  next h => have := p.outer_distance; omega

private theorem sideClear_target_remaining (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (AcceptanceSoundness.sideClearSchedule l p target) (targetHoles l p target)).remaining =
      targetHoles l p target \ Boundary.frame := by
  rw [AcceptanceSoundness.sideClearSchedule, emit_remaining_append]
  change ((emit (frameSchedule p.W p.H) (targetHoles l p target)).remaining.filter
    fun q => Direction.north.lane q ∉
      sideBands p (targetHoles l p target \ Boundary.frame).card) = _
  rw [Finset.filter_eq_self.mpr]
  · exact frame_remaining _ _ _
  · intro q hq hb
    have he := target_side_clear_empty l p hl ha target
    exact Finset.notMem_empty q (he ▸ Finset.mem_filter.mpr ⟨hq, hb⟩)

private theorem corridor_before_trim (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {a : PageColumn}
    (hac : a ∈ pageColumns l p side) (hpublic : a.privateColumn = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = a.column)
    (hy0 : 1 ≤ pageDepth p side q) (hy : pageDepth p side q < p.Y a.level) :
    q ∈ (emit (trimBeforeSchedule l p target side) (targetHoles l p target)).remaining := by
  obtain ⟨hj, hjm, hc0, hcW⟩ := pageColumn_bounds l p hl hM ha side hac
  have hY := readDepth_add_lt_D p a.level
  rw [readDepth_eq p hj hjm] at hY
  have hH : p.H = 2 * p.D := rfl
  have hrow := q.2.isLt
  have hframe : q ∉ Boundary.frame := by
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases side <;> cases d <;>
      simp only [pageDepth, reduceCtorEq, ite_true, ite_false, Boundary.edge,
        Finset.mem_filter, Finset.mem_univ, true_and] at hd hy0 hy <;> omega
  have htarget := pageColumn_corridor_target l p hl hM ha target side hac hpublic hx hy0 hy
  cases side with
  | lower =>
    simpa only [trimBeforeSchedule, reduceCtorEq, ite_false, List.append_nil,
      sideClear_target_remaining l p hl ha target] using Finset.mem_sdiff.mpr ⟨htarget, hframe⟩
  | upper =>
    rw [trimBeforeSchedule, ite_eq_left rfl, emit_remaining_append,
      sideClear_target_remaining l p hl ha target]
    simp only [emit_remaining, allRegions, Finset.union_empty]
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_sdiff.mpr ⟨htarget, hframe⟩, ?_⟩
    intro ht
    obtain ⟨b, hb, _, _, hdepth⟩ := (mem_trim_region l p .lower q).mp ht
    obtain ⟨hb0, hbm, _⟩ := pageColumn_bounds l p hl hM ha .lower hb
    have hbD := trimDepth_lt_D p hb0 hbm
    simp only [pageDepth, reduceCtorEq, ite_true, ite_false] at hy hdepth
    omega

private theorem corridor_card (p : Scales.Parameters) (side : Side) (a : PageColumn)
    (hc : a.column < p.W) (hY : p.Y a.level < p.H) :
    ((Finset.univ : Finset (Cell (p.W + 1) (p.H + 1))).filter fun q =>
      q.1.val = a.column ∧ 1 ≤ pageDepth p side q ∧ pageDepth p side q < p.Y a.level).card =
      p.Y a.level - 1 := by
  classical
  rw [← Nat.card_Ico 1 (p.Y a.level)]
  apply Finset.card_bij (fun q _ => pageDepth p side q)
  · intro q hq
    exact Finset.mem_Ico.mpr (Finset.mem_filter.mp hq).2.2
  · intro q hq r hr he
    obtain ⟨_, hqx, _, _⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hrx, _, _⟩ := Finset.mem_filter.mp hr
    apply Prod.ext (Fin.ext (hqx.trans hrx.symm))
    apply Fin.ext
    have hq' := q.2.isLt
    have hr' := r.2.isLt
    cases side <;> simp only [pageDepth, reduceCtorEq, ite_true, ite_false] at he <;> omega
  · intro v hv
    obtain ⟨hv0, hvY⟩ := Finset.mem_Ico.mp hv
    let q : Cell (p.W + 1) (p.H + 1) :=
      (⟨a.column, by omega⟩, ⟨if side = .upper then v else p.H - v, by split <;> omega⟩)
    have hdepth : pageDepth p side q = v := by
      cases side <;> simp only [q, pageDepth, reduceCtorEq, ite_true, ite_false]
      omega
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, rfl, by omega, by omega⟩, hdepth⟩

/-- The whole actual trim consumes at least the complete outer corridor in every public column. -/
theorem trim_target_column_loss (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {a : PageColumn}
    (hac : a ∈ pageColumns l p side) (hpublic : a.privateColumn = false) :
    let T := (emit (trimBeforeSchedule l p target side) (targetHoles l p target)).remaining
    let U := (emit [trimRound l p side] T).remaining
    (U.filter fun q => q.1.val = a.column).card + (p.Y a.level - 1) ≤
      (T.filter fun q => q.1.val = a.column).card := by
  classical
  dsimp only
  let T := (emit (trimBeforeSchedule l p target side) (targetHoles l p target)).remaining
  let U := (emit [trimRound l p side] T).remaining
  let B := (Finset.univ : Finset (Cell (p.W + 1) (p.H + 1))).filter fun q =>
    q.1.val = a.column ∧ 1 ≤ pageDepth p side q ∧ pageDepth p side q < p.Y a.level
  obtain ⟨hj, hjm, _, hc⟩ := pageColumn_bounds l p hl hM ha side hac
  have hY := readDepth_add_lt_H p a.level
  rw [readDepth_eq p hj hjm] at hY
  have hcard : B.card = p.Y a.level - 1 := corridor_card p side a hc (by omega)
  have hU : U = T \ (trimRound l p side).region := by
    simp only [U, emit_remaining, allRegions, Finset.union_empty]
  have hBT : B ⊆ T.filter fun q => q.1.val = a.column := by
    intro q hq
    obtain ⟨_, hx, hy0, hy⟩ := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨corridor_before_trim l p hl hM ha target side hac hpublic hx hy0 hy, hx⟩
  have hBR : B ⊆ (trimRound l p side).region := by
    intro q hq
    obtain ⟨_, hx, _, hy⟩ := Finset.mem_filter.mp hq
    exact (mem_trim_region l p side q).mpr
      ⟨a, hac, hpublic, hx, by have := trimDepth_gt_work p hj hjm; omega⟩
  have hUT : U.filter (fun q => q.1.val = a.column) ⊆ T.filter (fun q => q.1.val = a.column) := by
    rw [hU]
    exact Finset.filter_subset_filter _ Finset.sdiff_subset
  have hd : Disjoint (U.filter fun q => q.1.val = a.column) B := by
    apply Finset.disjoint_left.mpr
    intro q hq hb
    exact (Finset.mem_sdiff.mp (hU ▸ (Finset.mem_filter.mp hq).1)).2 (hBR hb)
  have hle := Finset.card_le_card (Finset.union_subset hUT hBT)
  rw [Finset.card_union_of_disjoint hd, hcard] at hle
  exact hle

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramLowerFinishStockLocation
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramThirdClear

/-! Every actual lower-finish reference front contains at most its one central-cut marker. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem upper_interlevel_above (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : pageDepth p .upper q = trimDepth p j) : q.2.val < p.D := by
  have h0 := readDepth_add_lt_D p j
  have h1 := readDepth_add_lt_D p (j + 1)
  rw [readDepth_eq p hj (by omega)] at h0
  rw [readDepth_eq p (by omega) (by omega)] at h1
  simp only [pageDepth, ite_true, trimDepth, ite_eq_left hjm] at hy
  omega

private theorem lower_interlevel_row (p : Scales.Parameters) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : pageDepth p .lower q = trimDepth p j) :
    q.2.val = p.H - (p.Y j + p.Y (j + 1)) / 2 := by
  have h0 := readDepth_add_lt_H p j
  have h1 := readDepth_add_lt_H p (j + 1)
  rw [readDepth_eq p hj (by omega)] at h0
  rw [readDepth_eq p (by omega) (by omega)] at h1
  simp only [pageDepth, reduceCtorEq, ite_false, trimDepth, ite_eq_left hjm] at hy
  have := q.2.isLt
  omega

private theorem work_half_not_private (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining)
    (hy : q.2.val = p.H - p.Y 1 / 2) (hx : q.1.val ∈ privateColumns l p) : False := by
  have hs : privateRound l p ∈ workReadSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    apply work_has_axis
    apply axis_has_prep
    apply prep_has_marker
    exact List.mem_cons_self ..
  apply emit_stage_excluded hs hq
  apply (private_region l p q).mpr ⟨hx, ?_⟩
  have hY := readDepth_add_lt_H p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hY
  rw [hy]
  omega

private theorem finish_column_aux (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (before after : List Template) (cols : Finset ℕ)
    (hs : pageChecks l p .lower ++ pageChecks l p .upper =
      before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: after)
    (x : ℕ) (hx : x ∈ cols) : x ∈ auxiliaries l p := by
  rcases lowerFinish_location l p before after cols hs x hx with h | ⟨j, _, _, hj, _⟩
  · exact (Finset.mem_sdiff.mp h).1
  · obtain ⟨a, ha', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hj)
    exact he ▸ l.acceptancePageColumn_aux p hl hM ha .lower (List.mem_filter.mp ha').1

private theorem lower_interlevel_excluded (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (before after : List Template) (cols : Finset ℕ)
    (hs : pageChecks l p .lower ++ pageChecks l p .upper =
      before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: after)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ cols)
    (hq : q ∈ (emit before ((emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining)).remaining)
    (hm : InterlevelMarker l p .lower q) : False := by
  obtain ⟨a, ha, hj, hjm, hax, hay⟩ := hm
  rcases lowerFinish_location l p before after cols hs q.1.val hx with hnot | ⟨j, hj', hjm', hc, hrow⟩
  · apply (Finset.mem_sdiff.mp hnot).2
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa only [decide_eq_true_eq] using And.intro hj hjm⟩, hax.symm⟩
  · obtain ⟨b, hb, hbx⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    obtain ⟨hb, hbj⟩ := List.mem_filter.mp hb
    have hbj : b.level = j := by simpa only [beq_iff_eq] using hbj
    have he := l.acceptanceLowerColumn_level p hl ha hb (hax.symm.trans hbx.symm)
    have hy := lower_interlevel_row p hj hjm hay
    rw [he, hbj] at hy
    exact emit_stage_excluded hrow hq
      ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr hy))

/-- A surviving target hole in an actual lower-finish front is its unique possible central-cut cell. -/
private theorem lowerFinish_target_front_row (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (before after : List Template) (cols : Finset ℕ)
    (hs : pageChecks l p .lower ++ pageChecks l p .upper =
      before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: after)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ cols)
    (hq : q ∈ (emit before ((emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining)).remaining)
    (hfront : prefixRank .south q < p.D + 1) : q.2.val = p.D := by
  have hwork : q ∈ (emit (workReadSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining := by
    have h := emit_remaining_subset _ _ hq
    rw [workSchedule, emit_remaining_append] at h
    exact emit_remaining_subset _ _ h
  have hsouth : p.D ≤ q.2.val := by
    simp only [prefixRank, Nat.add_sub_cancel] at hfront
    have hH : p.H = 2 * p.D := rfl
    omega
  have haux := finish_column_aux l p hl hM ha before after cols hs q.1.val hx
  cases workRead_inventory l p hl hM ha target hwork with
  | cut hy _ => exact hy
  | half hy hc =>
    rcases Finset.mem_union.mp hc with hcore | hprivate
    · exact False.elim (l.acceptanceAux_not_core p hl haux hcore)
    · exact False.elim (work_half_not_private l p target hwork hy hprivate)
  | interlevel side hm =>
    cases side with
    | upper =>
      obtain ⟨a, _, hj, hjm, _, hy⟩ := hm
      have hn := upper_interlevel_above p hj hjm hy
      omega
    | lower => exact False.elim (lower_interlevel_excluded l p hl before after cols hs target hx hq hm)

/-- The literal reference front of every selected lower-finish column contains at most one target hole. -/
theorem lowerFinish_target_front_card_le_one (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (target : List Bool) (before after : List Template) (cols : Finset ℕ)
    (hs : pageChecks l p .lower ++ pageChecks l p .upper =
      before ++ .read .south (prefixRequests cols fun _ => p.D + 1) :: after)
    (x : ℕ) (hx : x ∈ cols) :
    (((emit before ((emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).remaining)).remaining).filter fun q =>
        q.1.val = x ∧ prefixRank .south q < p.D + 1).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha' b hb'
  obtain ⟨haE, hax, haf⟩ := Finset.mem_filter.mp ha'
  obtain ⟨hbE, hbx, hbf⟩ := Finset.mem_filter.mp hb'
  have hay := lowerFinish_target_front_row l p hl hM ha target before after cols hs (hax ▸ hx) haE haf
  have hby := lowerFinish_target_front_row l p hl hM ha target before after cols hs (hbx ▸ hx) hbE hbf
  exact Prod.ext (Fin.ext (hax.trans hbx.symm)) (Fin.ext (hay.trans hby.symm))

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockWork
public import Push.AcceptanceProgramComplete
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramLower

/-! The actual literal page-check prefix before each matching interlevel row. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private def checkHead (l : PortLayout) (p : Scales.Parameters) (side : Side) : List Template :=
  if side = .lower then
    [lowerFinish p (auxiliaries l p \ live l p side),
      readRows p .west {p.H - p.Y 1 / 2}, .clear .north (cores l p)]
  else [.clear .north (auxiliaries l p \ live l p side)]

private def checkPair (l : PortLayout) (p : Scales.Parameters) (side : Side) (k : ℕ) : List Template :=
  [readRows p .west {interlevelRow p side (k + 1)},
    if side = .lower then lowerFinish p (levelColumns l p side (k + 1))
      else .clear .north (levelColumns l p side (k + 1))]

private theorem pageChecks_eq (l : PortLayout) (p : Scales.Parameters) (side : Side) :
    pageChecks l p side = checkHead l p side ++ (List.range (p.levels - 1)).flatMap (checkPair l p side) := rfl

/-- The exact number of page-check blocks preceding the matching physical marker row. -/
@[expose] def interlevelIndex (l : PortLayout) (p : Scales.Parameters) (side : Side) (j : ℕ) : ℕ :=
  if side = .lower then 2 * j + 1 else (pageChecks l p .lower).length + 2 * j - 1

/-- The actual page-check templates before that page and level's literal horizontal read. -/
@[expose] def interlevelPrefix (l : PortLayout) (p : Scales.Parameters) (side : Side) (j : ℕ) : List Template :=
  (pageChecks l p .lower ++ pageChecks l p .upper).take (interlevelIndex l p side j)

private def beforeChecks (l : PortLayout) (p : Scales.Parameters) (side : Side) (j : ℕ) : List Template :=
  (if side = .upper then pageChecks l p .lower else []) ++ checkHead l p side ++
    (List.range (j - 1)).flatMap (checkPair l p side)

private theorem beforeChecks_length (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) : (beforeChecks l p side j).length = interlevelIndex l p side j := by
  cases side <;> simp [beforeChecks, interlevelIndex, checkHead, checkPair, List.length_flatMap,
    Nat.mul_comm] <;> omega

private theorem pageChecks_split (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    ∃ after, pageChecks l p .lower ++ pageChecks l p .upper =
      beforeChecks l p side j ++ readRows p .west {interlevelRow p side j} :: after := by
  have hsplit : List.range (p.levels - 1) = List.range (j - 1) ++
      ((j - 1) :: ((List.range (p.levels - j - 1)).map fun k => j + k)) := by
    have he : p.levels - 1 = (j - 1) + (1 + (p.levels - j - 1)) := by omega
    rw [he, List.range_add]
    simp only [List.range_add, List.range_one, List.map_cons, List.map_map,
      List.cons_append, List.nil_append, Nat.add_zero]
    congr 2
    apply List.map_congr_left
    intro k _
    dsimp only [Function.comp_apply]
    omega
  have hj' : j - 1 + 1 = j := by omega
  cases side
  · refine ⟨.clear .north (levelColumns l p .upper j) ::
        (((List.range (p.levels - j - 1)).map fun k => j + k).flatMap (checkPair l p .upper)), ?_⟩
    rw [pageChecks_eq l p .upper, hsplit]
    simp only [beforeChecks, checkPair, interlevelRow, ite_true, reduceCtorEq, ite_false,
      List.flatMap_append, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc, hj']
  · refine ⟨lowerFinish p (levelColumns l p .lower j) ::
        ((((List.range (p.levels - j - 1)).map fun k => j + k).flatMap (checkPair l p .lower)) ++
          pageChecks l p .upper), ?_⟩
    rw [pageChecks_eq l p .lower, hsplit]
    simp only [beforeChecks, checkPair, interlevelRow, ite_true, reduceCtorEq, ite_false,
      List.flatMap_append, List.flatMap_cons, List.cons_append, List.nil_append, List.append_assoc,
      List.nil_append, hj']

private theorem interlevelPrefix_eq (l : PortLayout) (p : Scales.Parameters) (side : Side) {j : ℕ}
    (hj : 1 ≤ j) (hjm : j < p.levels) :
    interlevelPrefix l p side j = beforeChecks l p side j := by
  obtain ⟨after, he⟩ := pageChecks_split l p side hj hjm
  unfold interlevelPrefix
  rw [he, ← beforeChecks_length l p side hj, List.take_left]

private theorem marker_not_finish (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) (cols : Finset ℕ)
    (hlower : side = .lower → q.1.val ∉ cols) : ReadAvoids q (lowerFinish p cols) := by
  intro hread
  obtain ⟨⟨lane, span⟩, hreq, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hread
  obtain ⟨hcol', hspan⟩ := (mem_prefixRequests _ _ _ _).mp hreq
  change q.1.val = lane at hcol
  cases side with
  | lower => exact hlower rfl (hcol.symm ▸ hcol')
  | upper =>
    obtain ⟨_, _, hj, hjm, _, hy⟩ := hm
    have hrow := marker_row p .upper hj hjm hy
    have hb := interlevelDepth_bounds p hj hjm
    have hh : p.H = 2 * p.D := rfl
    simp only [interlevelRow, ite_true] at hrow
    simp only [prefixRank, Nat.add_sub_cancel, hspan] at hpos
    omega

private theorem marker_avoids_head (l : PortLayout) (p : Scales.Parameters) (side readSide : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q) :
    ∀ stage ∈ checkHead l p readSide, ReadAvoids q stage := by
  obtain ⟨a, ha, hj, hjm, hx, hy⟩ := hm
  have hm : InterlevelMarker l p side q := ⟨a, ha, hj, hjm, hx, hy⟩
  have hfinish : ReadAvoids q (lowerFinish p (auxiliaries l p \ live l p .lower)) := by
    apply marker_not_finish l p side hm
    intro hs hc
    subst side
    apply (Finset.mem_sdiff.mp hc).2
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa only [decide_eq_true_eq] using And.intro hj hjm⟩, hx.symm⟩
  have hhalf : ReadAvoids q (readRows p .west {p.H - p.Y 1 / 2}) := by
    intro hr
    have he := Finset.mem_singleton.mp ((readRows_region p .west _ (Or.inl rfl) q).mp hr)
    have hrow := marker_row p side hj hjm hy
    exact (interlevelRow_ne_cut_half p side hj hjm).2 (hrow.symm.trans he)
  cases readSide <;> simp only [checkHead, ite_true, reduceCtorEq, ite_false,
    List.forall_mem_cons, List.not_mem_nil, forall_false, hfinish, hhalf, true_and]
  all_goals constructor
  all_goals first | exact trivial | exact fun _ => trivial

private theorem marker_avoids_pair (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side readSide : Side) {a : PageColumn} (ha : a ∈ pageColumns l p side)
    (hj : 1 ≤ a.level) (hjm : a.level < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = a.column) (hy : pageDepth p side q = trimDepth p a.level) {k : ℕ}
    (hk : k + 1 < p.levels) (hbefore : side ≠ readSide ∨ k + 1 < a.level) :
    ∀ stage ∈ checkPair l p readSide k, ReadAvoids q stage := by
  have hm : InterlevelMarker l p side q := ⟨a, ha, hj, hjm, hx, hy⟩
  have hrow := marker_row p side hj hjm hy
  have hread : ReadAvoids q (readRows p .west {interlevelRow p readSide (k + 1)}) := by
    intro hr
    have he := Finset.mem_singleton.mp ((readRows_region p .west _ (Or.inl rfl) q).mp hr)
    obtain ⟨hs, hj'⟩ := (interlevelRow_eq_iff p side readSide hj hjm (by omega) hk).mp (hrow.symm.trans he)
    rcases hbefore with hbefore | hbefore
    · exact hbefore hs
    · omega
  cases readSide with
  | upper =>
    simp only [checkPair, reduceCtorEq, ite_false, List.forall_mem_cons, List.not_mem_nil,
      forall_false, hread, true_and]
    exact ⟨trivial, fun _ => trivial⟩
  | lower =>
    have hfinish : ReadAvoids q (lowerFinish p (levelColumns l p .lower (k + 1))) := by
      apply marker_not_finish l p side hm
      intro hs hc
      subst side
      obtain ⟨b, hb, hxb⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
      obtain ⟨hb, hbj⟩ := List.mem_filter.mp hb
      have hbj : b.level = k + 1 := of_decide_eq_true hbj
      have he := l.acceptanceLowerColumn_level p hl ha hb (hx.symm.trans hxb.symm)
      rcases hbefore with hn | hbefore
      · exact hn rfl
      · omega
    simp only [checkPair, ite_true, List.forall_mem_cons, List.not_mem_nil,
      forall_false, hread, hfinish, true_and]
    exact fun _ => trivial

private theorem marker_avoids_before (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) {a : PageColumn} (ha : a ∈ pageColumns l p side)
    (hj : 1 ≤ a.level) (hjm : a.level < p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = a.column) (hy : pageDepth p side q = trimDepth p a.level) :
    ∀ stage ∈ beforeChecks l p side a.level, ReadAvoids q stage := by
  have hm : InterlevelMarker l p side q := ⟨a, ha, hj, hjm, hx, hy⟩
  have hhead := marker_avoids_head l p side side hm
  have hprior : ∀ stage ∈ (List.range (a.level - 1)).flatMap (checkPair l p side), ReadAvoids q stage := by
    intro stage hs
    obtain ⟨k, hk, hs⟩ := List.mem_flatMap.mp hs
    have hk := List.mem_range.mp hk
    exact marker_avoids_pair l p hl side side ha hj hjm hx hy (by omega) (Or.inr (by omega)) stage hs
  have hearlier : ∀ stage ∈ (if side = .upper then pageChecks l p .lower else []), ReadAvoids q stage := by
    cases side with
    | upper =>
      rw [ite_eq_left rfl, pageChecks_eq]
      rw [List.forall_mem_append]
      refine ⟨marker_avoids_head l p .upper .lower hm, ?_⟩
      intro stage hs
      obtain ⟨k, hk, hs⟩ := List.mem_flatMap.mp hs
      have hk := List.mem_range.mp hk
      exact marker_avoids_pair l p hl .upper .lower ha hj hjm hx hy (by omega) (Or.inl (by decide)) stage hs
    | lower => simp only [reduceCtorEq, ite_false, List.not_mem_nil, forall_false]; exact fun _ => trivial
  exact List.forall_mem_append.mpr ⟨List.forall_mem_append.mpr ⟨hearlier, hhead⟩, hprior⟩

private theorem interlevelPrefix_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) (j : ℕ) :
    (emit (interlevelPrefix l p side j)
      (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target)).remaining).discarded = 0 := by
  have hz := schedule_discarded_zero l p hl hM haxes target
  rw [schedule_eq_lower_upper, lowerSchedule, List.append_assoc, emit_discarded_append] at hz
  have hp : (emit (pageChecks l p .lower ++ pageChecks l p .upper)
      (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target)).remaining).discarded = 0 := by omega
  rw [← List.take_append_drop (interlevelIndex l p side j) (pageChecks l p .lower ++ pageChecks l p .upper),
    emit_discarded_append] at hp
  unfold interlevelPrefix
  omega

/-- A matching canonical fixed marker remains present immediately before its literal page-check row is read. -/
theorem interlevelMarker_prefix_remaining (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p side q)
    (hy : q.2.val = interlevelRow p side j) :
    q ∈ (emit (interlevelPrefix l p side j)
      (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target)).remaining).remaining := by
  have hwork := interlevelMarker_work_remaining l p hl hM haxes target side hm
  apply emit_mem_of_no_reads _ _ (interlevelPrefix_discarded_zero l p hl hM haxes target side j) hwork
  obtain ⟨a, ha, hlow, hhigh, hx, hd⟩ := hm
  have hrow := marker_row p side hlow hhigh hd
  have hj' := ((interlevelRow_eq_iff p side side hlow hhigh hj hjm).mp (hrow.symm.trans hy)).2
  rw [interlevelPrefix_eq l p side hj hjm, ← hj']
  intro d requests hs
  exact marker_avoids_before l p hl side ha hlow hhigh hx hd (.read d requests) hs

/-- On each actual marker-read input row the canonical reference stock is exactly its same-page, same-level metadata. -/
theorem interlevel_target_row_iff (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (side : Side) {j : ℕ} (hj : 1 ≤ j) (hjm : j < p.levels)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = interlevelRow p side j) :
    q ∈ (emit (interlevelPrefix l p side j)
      (emit (workSchedule l p (targetHoles l p target \ Boundary.frame).card)
        (targetHoles l p target)).remaining).remaining ↔
      ∃ a ∈ pageColumns l p side, a.level = j ∧ q.1.val = a.column := by
  constructor
  · intro hq
    obtain ⟨a, ha, he, hx, _⟩ := interlevel_target_residual_metadata l p hl hM haxes target
      (interlevelPrefix l p side j) side hj hjm hq hy
    exact ⟨a, ha, he, hx⟩
  · rintro ⟨a, ha, hlevel, hx⟩
    apply interlevelMarker_prefix_remaining l p hl hM haxes target side hj hjm _ hy
    refine ⟨a, ha, hlevel ▸ hj, hlevel ▸ hjm, hx, ?_⟩
    rw [hlevel]
    have hb := interlevelDepth_bounds p hj hjm
    unfold interlevelDepth at hb
    have hh : p.H = 2 * p.D := rfl
    cases side <;> simp only [pageDepth, interlevelRow, trimDepth, ite_eq_left hjm,
      interlevelDepth, ite_true, reduceCtorEq, ite_false] at hy ⊢ <;> omega

end PushPuzzle.Push.AcceptanceProgram

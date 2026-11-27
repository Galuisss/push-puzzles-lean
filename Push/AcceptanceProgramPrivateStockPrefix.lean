/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramPrivateStock
public import Push.AcceptanceProgramHalfStock
import all Push.AcceptanceProgramHalfStockGeometry
import all Push.AcceptanceProgramInterlevelStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramLayout
import all PushS.PortLayoutCoordinates

/-! The real first nine blocks preserve every represented hole in the owned private depth window. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem south_region_mono {p : Scales.Parameters} {q a : Cell (p.W + 1) (p.H + 1)}
    (requests : List (ℕ × ℕ)) (hx : q.1 = a.1) (hy : p.H - a.2.val ≤ p.H - q.2.val)
    (hq : q ∈ readRegion .south requests) : a ∈ readRegion .south requests := by
  obtain ⟨request, hr, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hq
  apply (mem_readRegion _ _ a).mpr
  refine ⟨request, hr, ?_, ?_⟩
  · change a.1.val = request.1
    exact (congrArg Fin.val hx).symm.trans hcol
  · simp only [prefixRank, Nat.add_sub_cancel] at hpos ⊢
    omega

private theorem north_trim_avoids_private (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hshort : p.H - q.2.val ≤ p.Y 1 + 2) : q ∉ (trimRound l p .upper).region := by
  intro hr
  obtain ⟨a, ha, _, _, hd⟩ := (mem_trim_region l p .upper q).mp hr
  have hb := l.acceptancePageColumn_level_bounds p hl hM .upper ha
  have ht := trimDepth_lt_D p hb.1
  have hy := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hy
  have hh : p.H = 2 * p.D := rfl
  change q.2.val < trimDepth p a.level at hd
  have hq := q.2.isLt
  omega

private theorem north_main_avoids_private (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (hshort : p.H - q.2.val ≤ p.Y 1 + 2) : q ∉ (mainRound l p .upper).region := by
  intro hr
  obtain ⟨_, hreq, _, hpos⟩ := (mem_readRegion _ _ q).mp hr
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hreq
  have hb := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  have heD := readDepth_add_lt_D p e.level
  rw [readDepth_eq p hb.1 hb.2] at heD
  have hy := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hy
  have hh : p.H = 2 * p.D := rfl
  change q.2.val < p.Y e.level + 2 at hpos
  have hq := q.2.isLt
  omega

/-- Every actual canonical target hole between half-depth and the private branch survives until its real cap read. -/
theorem private_window_before_private (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)}
    (hq : q ∈ targetHoles l p target) (hx : q.1.val ∈ privateColumns l p)
    (hlow : p.Y 1 / 2 ≤ pageDepth p .lower q) (hhigh : pageDepth p .lower q ≤ p.Y 1 + 2) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 9)
      (targetHoles l p target)).remaining := by
  have hs : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 9 =
      secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card := by
    simp [schedule, List.take_append, preparation_length, preparation_take_nine]
  rw [hs]
  have hY := p.Y_ge 1
  have hD := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hD
  have hh : p.H = 2 * p.D := rfl
  change p.Y 1 / 2 ≤ p.H - q.2.val at hlow
  change p.H - q.2.val ≤ p.Y 1 + 2 at hhigh
  let a : Cell (p.W + 1) (p.H + 1) := (q.1, ⟨p.H - p.Y 1 / 2, by omega⟩)
  have ha : a.2.val = p.H - p.Y 1 / 2 := rfl
  have hxa : a.1.val ∈ cores l p ∪ privateColumns l p := Finset.mem_union_right _ hx
  have htrimL : ReadAvoids q (trimRound l p .lower) := fun hr =>
    half_not_trim l p hl hM .lower ha hxa (south_region_mono (q := q) (a := a) _ rfl (by dsimp [a]; omega) hr)
  have hmainL : ReadAvoids q (mainRound l p .lower) := fun hr =>
    half_not_main l p hl hM .lower ha hxa (south_region_mono (q := q) (a := a) _ rfl (by dsimp [a]; omega) hr)
  have htrimU : ReadAvoids q (trimRound l p .upper) := north_trim_avoids_private l p hl hM hhigh
  have hmainU : ReadAvoids q (mainRound l p .upper) := north_main_avoids_private l p hl hM hhigh
  have hframe : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
    have hn := half_not_frame l p hl haxes ha hxa
    have hnotzero : q.1.val ≠ 0 := fun he => hn ((Boundary.mem_frame a).mpr
      ⟨.west, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; exact he⟩)
    have hnotwidth : q.1.val ≠ p.W := fun he => hn ((Boundary.mem_frame a).mpr
      ⟨.east, by simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and]; change q.1.val + 1 = p.W + 1; omega⟩)
    intro stage hs
    simp only [frameSchedule, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals intro hr
    all_goals obtain ⟨⟨lane, span⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
    · change q.1.val = lane at hcol
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact hnotzero hcol
      · exact hnotwidth hcol
    · change q.2.val = lane at hcol
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  apply emit_mem_of_no_reads _ _ (secondRows_discarded_zero l p hl hM haxes target) hq
  have hall : ∀ stage ∈ secondRowSchedule l p (targetHoles l p target \ Boundary.frame).card,
      ReadAvoids q stage := by
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false,
      true_and, htrimU, htrimL, hmainU, hmainL]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial | trivial
  exact fun d requests h => hall (.read d requests) h

end PushPuzzle.Push.AcceptanceProgram

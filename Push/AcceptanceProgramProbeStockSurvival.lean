/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramProbeStockSignals
public import Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramInterlevelStockReads
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramFirstClear
import all Push.AcceptanceProgramSecondClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProbePartners
import all PushS.PortFixedSeparation
import all PushS.PortLayoutCoordinates

/-! True principal-axis Y+2 probes survive every literal preparation read and zero-loss clear. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe AcceptanceProbe

private theorem probeCell_preparation_avoids (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (i : Fin l.portCount) (k : ℕ) :
    ∀ stage ∈ preparation l p k, ReadAvoids (probeCell l p hl hM haxes i) stage := by
  let q := probeCell l p hl hM haxes i
  obtain ⟨he, hs, hp⟩ := upperEndpoint_spec l hl i
  have hb := probeLevel_bounds l p hl hM i
  have hY := readDepth_add_lt_D p (level l hl i)
  rw [readDepth_eq p hb.1 hb.2] at hY
  have hYpos := p.Y_ge (level l hl i)
  have hx0 := readLength_add_lt_x p i.val 0
  have hxW := x_add_readLength_lt_W p (i.isLt.trans_le haxes) 0
  have hD : 0 < p.D := by have h := p.outer_distance; omega
  have hH : p.H = 2 * p.D := rfl
  have hqx : q.1.val = p.x i.val := rfl
  have hqy : q.2.val = p.Y (level l hl i) + 2 := rfl
  have haxis : q.1.val ∈ axes l p := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨i.val, List.mem_range.mpr i.isLt, rfl⟩)
  have hnotprivate : q.1.val ∉ privateColumns l p := by
    intro hpriv
    have haux := private_column_aux l p hl hM haxes hpriv
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis)
  have hnotguard : q.1.val ∉ guards l p :=
    l.acceptanceStreet_not_guard p (axis_in_streetColumns l p i.isLt)
  have htrim (side : Side) : ReadAvoids q (trimRound l p side) := by
    intro hr
    obtain ⟨a, ha, _, hx, _⟩ := (mem_trim_region l p side q).mp hr
    have haux := hx.symm ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis)
  have hmainU : ReadAvoids q (mainRound l p .upper) := by
    intro hr
    obtain ⟨_, hreq, hcol, hpos⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨e, hefilter, rfl⟩ := List.mem_map.mp hreq
    obtain ⟨he', hs'⟩ := List.mem_filter.mp hefilter
    have hs' : e.side = .upper := by simpa only [beq_iff_eq] using hs'
    have hport : e.port = (upperEndpoint l hl i).port := by
      change q.1.val = p.x e.port at hcol
      rw [hqx] at hcol
      have h := Nat.mul_right_cancel hD hcol
      omega
    have heq := l.endpoints_key_injective hl he' he (hs'.trans hs.symm) hport
    change q.2.val < p.Y e.level + 2 at hpos
    rw [heq] at hpos
    change q.2.val < p.Y (level l hl i) + 2 at hpos
    omega
  have hmainL : ReadAvoids q (mainRound l p .lower) := by
    intro hr
    obtain ⟨_, hreq, _, hpos⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨e, hefilter, rfl⟩ := List.mem_map.mp hreq
    have helevel := l.endpoints_level_bounds p hl hM (List.mem_filter.mp hefilter).1
    have heD := readDepth_add_lt_D p e.level
    rw [readDepth_eq p helevel.1 helevel.2] at heD
    change p.H + 1 - 1 - q.2.val < p.Y e.level + 2 at hpos
    omega
  have hprivate : ReadAvoids q (privateRound l p) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnotprivate
  have hguard : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnotguard
  have hflank : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) := by
    apply avoid_whole_rows .east (Or.inr rfl)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hguardRow : ReadAvoids q (readRows p .west {p.D - 4}) := by
    apply avoid_whole_rows .west (Or.inl rfl)
    simp only [Finset.mem_singleton]
    omega
  have hframe : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
    intro stage hs
    simp only [frameSchedule, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals intro hr
    all_goals obtain ⟨⟨lane, span⟩, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hr
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hreq
    · change q.1.val = lane at hcol
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
    · change q.2.val = lane at hcol
      rcases hreq with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> omega
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  have htrimU := htrim .upper
  have htrimL := htrim .lower
  change ∀ stage ∈ preparation l p k, ReadAvoids q stage
  simp only [preparation_eq_secondRows, secondRowSchedule, mainAxisSchedule, firstRowSchedule,
    firstTrimSchedule, markerPreparation, List.forall_mem_append, List.forall_mem_cons,
    List.not_mem_nil, forall_false, htrimU, htrimL, hmainU, hmainL, hprivate, hguard,
    hflank, hguardRow, hclear, true_and]
  repeat' apply And.intro
  all_goals first | exact hframe | exact fun _ => trivial

/-- Every true-bit probe remains in the real canonical reference after all thirteen preparation blocks. -/
theorem probeSignalStock_preparation_remaining (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes) (target : List Bool) :
    probeSignalStock l p hl hM haxes target ⊆
      (emit (preparation l p (targetHoles l p target \ Boundary.frame).card) (targetHoles l p target)).remaining := by
  intro q hq
  have hsignal := (signal_probe_rows l p hl hM haxes target).mpr hq
  have htarget : q ∈ targetHoles l p target := by
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ _).mp hsignal.1
    exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ hs, hc⟩
  apply emit_mem_of_no_reads _ _ (preparation_discarded_zero l p hl hM haxes target) htarget
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hq
  intro side requests hs
  exact probeCell_preparation_avoids l p hl hM haxes i _ (.read side requests) hs

end PushPuzzle.Push.AcceptanceProgram

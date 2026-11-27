/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramMainStock
public import Push.AcceptanceProgramProbeStockSurvival
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramLayout
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! The literal R15 axis input and survival of an ordinary lower endpoint's optional tip. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- The actual reference prefix preceding the ordinary/core combined axis read. -/
@[expose] def axisReadBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) : List Template :=
  (schedule l p (targetHoles l p target \ Boundary.frame).card).take 15

/-- Preparation is followed by the upper probe-row read and its zero-loss clear before R15. -/
theorem axisReadBefore_eq (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    axisReadBefore l p target = preparation l p (targetHoles l p target \ Boundary.frame).card ++
      [readRows p .west (probeRows l p), .clear .east (probeRows l p)] := by
  simp only [axisReadBefore, schedule, preparation, frameSchedule]
  simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]

private theorem mainRound_mem_axisReadBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    (side : Side) : mainRound l p side ∈ axisReadBefore l p target := by
  cases side with
  | upper =>
    simp only [axisReadBefore, schedule, preparation, frameSchedule, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
    iterate 6 apply List.mem_cons_of_mem
    exact List.mem_cons_self
  | lower =>
    simp only [axisReadBefore, schedule, preparation, frameSchedule, List.cons_append,
      List.nil_append, List.take_succ_cons, List.take_zero]
    iterate 7 apply List.mem_cons_of_mem
    exact List.mem_cons_self

private theorem probe_mem_axisReadBefore (l : PortLayout) (p : Scales.Parameters) (target : List Bool) :
    readRows p .west (probeRows l p) ∈ axisReadBefore l p target := by
  rw [axisReadBefore_eq]
  exact List.mem_append_right _ (List.mem_cons_self ..)

/-- A false target bit emits the lower optional third-axis hole. -/
private theorem lower_axis_tip_target (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints)
    (hs : e.side = .lower) (hb : target.getD e.port false = false)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val = p.x e.port)
    (hy : q.2.val = p.H - (p.Y e.level + 2)) : q ∈ targetHoles l p target := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_add_lt_H p e.level
  rw [readDepth_eq p hj hjm] at hY
  have haxis : (q.1.val, q.2.val) ∈ pointHoles
      ((endpointSegments (coordinates p) (l.canonical target) e).take 1) := by
    rw [axis_mem]
    have hbit : (l.canonical target).axes.getD e.port false = false := hb
    simp only [hs, reduceCtorEq, ite_false, hbit, Bool.not_false, Bool.toNat_true,
      readDepth_eq p hj hjm, onSide, coordinates, hy]
    exact ⟨hx, by omega, by omega⟩
  obtain ⟨s, hseg, hc⟩ := (mem_pointHoles _ _).mp haxis
  exact (SegmentRecipe.mem_holes _ q).mpr ⟨s, List.mem_append_right _ (List.mem_append_left _
    (List.mem_flatMap.mpr ⟨e, he, List.mem_of_mem_take hseg⟩)), hc⟩

/-- The actual lower optional tip avoids every literal read preceding the combined axis block. -/
theorem lower_axis_tip_before (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) (e : Endpoint) (he : e ∈ l.endpoints) (hs : e.side = .lower)
    (hb : target.getD e.port false = false) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x e.port) (hy : q.2.val = p.H - (p.Y e.level + 2)) :
    q ∈ (emit (axisReadBefore l p target) (targetHoles l p target)).remaining := by
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM he
  have hY := readDepth_add_lt_D p e.level
  rw [readDepth_eq p hj hjm] at hY
  have hpos := p.Y_ge e.level
  have hH : p.H = 2 * p.D := rfl
  have hx0 := readLength_add_lt_x p e.port 0
  have hxW := x_add_readLength_lt_W p ((l.endpoints_port_lt hl he).trans_le haxes) 0
  have haxis : q.1.val ∈ axes l p := List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl he), hx.symm⟩)
  have hnotprivate : q.1.val ∉ privateColumns l p := by
    intro hp
    exact (Finset.mem_sdiff.mp (private_column_aux l p hl hM haxes hp)).2 (Finset.mem_union_left _ haxis)
  have hnotguard : q.1.val ∉ guards l p := by
    intro hg
    have hf := l.acceptanceGuard_street_far p hg (axis_in_streetColumns l p (l.endpoints_port_lt hl he))
    rw [hx, Nat.dist_self] at hf
    omega
  have htrim (side : Side) : ReadAvoids q (trimRound l p side) := by
    intro hr
    obtain ⟨a, ha, _, hcol, _⟩ := (mem_trim_region l p side q).mp hr
    have haux := hcol.symm ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis)
  have hmainL : ReadAvoids q (mainRound l p .lower) := by
    rw [← hs]
    intro hr
    have hdepth := (mainRound_column_region l p hl e he hx).mp hr
    simp only [pageDepth, hs, reduceCtorEq, ite_false] at hdepth
    omega
  have hmainU : ReadAvoids q (mainRound l p .upper) := by
    intro hr
    obtain ⟨_, hreq, _, hdepth⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hreq
    obtain ⟨hfj, hfm⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp hf).1
    have hFY := readDepth_add_lt_D p f.level
    rw [readDepth_eq p hfj hfm] at hFY
    change q.2.val < p.Y f.level + 2 at hdepth
    omega
  have hprivate : ReadAvoids q (privateRound l p) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnotprivate
  have hguard : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnotguard
  have hflanks : ReadAvoids q (readRows p .east {p.D - 2, p.D + 2}) := by
    apply avoid_whole_rows .east (Or.inr rfl)
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  have hminus : ReadAvoids q (readRows p .west {p.D - 4}) := by
    apply avoid_whole_rows .west (Or.inl rfl)
    simp only [Finset.mem_singleton]
    omega
  have hprobe : ReadAvoids q (readRows p .west (probeRows l p)) := by
    apply avoid_whole_rows .west (Or.inl rfl)
    intro hr
    obtain ⟨f, hf, hrow⟩ := List.mem_map.mp (List.mem_toFinset.mp hr)
    obtain ⟨hfj, hfm⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp hf).1
    have hFY := readDepth_add_lt_D p f.level
    rw [readDepth_eq p hfj hfm] at hFY
    omega
  have hframe : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
    apply frame_avoids p
    intro hf
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd <;> omega
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  apply emit_mem_of_no_reads _ _ (take_discarded_zero l p hl hM haxes target 15)
    (lower_axis_tip_target l p hl hM target e he hs hb hx hy)
  have hall : ∀ stage ∈ axisReadBefore l p target, ReadAvoids q stage := by
    rw [axisReadBefore_eq, preparation_eq_secondRows]
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule, markerPreparation]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false]
    simp only [hclear, htrim, hmainL, hmainU, hprivate, hguard, hflanks, hminus, hprobe, true_and]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial
  exact fun side requests h => hall (.read side requests) h

end PushPuzzle.Push.AcceptanceProgram

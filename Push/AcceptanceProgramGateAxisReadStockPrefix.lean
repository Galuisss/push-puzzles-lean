/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramAxisReadStockPrefix
public import PushS.PortGateAxis
import all Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceProgramMainStockGeometry
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramLayout
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-! The actual lower core near-axis trace survives until the combined axis read. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushFS.Reduction PushS PushS.PortLayout SegmentRecipe

/-- Canonical lower-axis holes from the work row through depth plus two survive to the combined axis block. -/
theorem gate_axis_lower_band_before (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x (g.left + 1))
    (hy : p.H - (p.Y 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - p.Y 1)
    (htarget : q ∈ targetHoles l p target) :
    q ∈ (emit (axisReadBefore l p target) (targetHoles l p target)).remaining := by
  have hj : 1 ≤ 1 := le_rfl
  have hjm := p.levels_pos
  have hi := gate_middle_lt l hl (placement_gate_mem l hg hk)
  have hY := readDepth_add_lt_D p 1
  rw [readDepth_eq p hj hjm] at hY
  have hpos := p.Y_ge 1
  have hH : p.H = 2 * p.D := rfl
  have hx0 := readLength_add_lt_x p (g.left + 1) 0
  have hxW := x_add_readLength_lt_W p (hi.trans_le haxes) 0
  have haxis : q.1.val ∈ axes l p := List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨g.left + 1, List.mem_range.mpr hi, hx.symm⟩)
  have hnotprivate : q.1.val ∉ privateColumns l p := by
    intro hp
    exact (Finset.mem_sdiff.mp (private_column_aux l p hl hM haxes hp)).2 (Finset.mem_union_left _ haxis)
  have hnotguard : q.1.val ∉ guards l p := by
    intro hg
    have hf := l.acceptanceGuard_street_far p hg (axis_in_streetColumns l p hi)
    rw [hx, Nat.dist_self] at hf
    omega
  have htrim (side : Side) : ReadAvoids q (trimRound l p side) := by
    intro hr
    obtain ⟨a, ha, _, hcol, _⟩ := (mem_trim_region l p side q).mp hr
    have haux := hcol.symm ▸ l.acceptancePageColumn_aux p hl hM haxes side ha
    exact (Finset.mem_sdiff.mp haux).2 (Finset.mem_union_left _ haxis)
  have hmainL : ReadAvoids q (mainRound l p .lower) := by
    intro hr
    obtain ⟨_, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hr
    obtain ⟨e, hefilter, rfl⟩ := List.mem_map.mp hreq
    obtain ⟨he, hs⟩ := List.mem_filter.mp hefilter
    have hs : e.side = .lower := by simpa only [beq_iff_eq] using hs
    have hport : e.port = g.left + 1 := by
      apply axis_injective p
      exact hcol.symm.trans hx
    exact l.endpoints_lower_ne_gate_middle hl (placement_gate_mem l hg hk) he hs hport
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
    htarget
  have hall : ∀ stage ∈ axisReadBefore l p target, ReadAvoids q stage := by
    rw [axisReadBefore_eq, preparation_eq_secondRows]
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule, markerPreparation]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false]
    simp only [hclear, htrim, hmainL, hmainU, hprivate, hguard, hflanks, hminus, hprobe, true_and]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial
  exact fun side requests h => hall (.read side requests) h

/-- The actual lower core near-axis trace is retained until R15. -/
theorem gate_axis_near_before (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {g : Placement} (hg : g ∈ placements l)
    {kind : Shuttle.Kind} (hk : g.gate = some kind) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val = p.x (g.left + 1))
    (hy : p.H - (p.Y 1 + 2) ≤ q.2.val ∧ q.2.val ≤ p.H - (p.Y 1 + 1))
    (htarget : q ∈ targetHoles l p target) :
    q ∈ (emit (axisReadBefore l p target) (targetHoles l p target)).remaining :=
  gate_axis_lower_band_before l p hl hM haxes target hg hk hx ⟨hy.1, by omega⟩ htarget

end PushPuzzle.Push.AcceptanceProgram

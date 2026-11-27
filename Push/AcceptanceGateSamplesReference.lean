/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceGateSamplesGeometry
public import Push.AcceptanceProgramAxisReadStockPrefix
import all Push.AcceptanceSoundnessSupportMarkerResidual
import all Push.AcceptanceSoundnessCentralSamples
import all Push.AcceptanceProgramGuardStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramNarrowSignals
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments

/-! The two independent sample columns retain their canonical lower work-band stock until R21. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout AcceptanceSoundness

/-- Canonical target holes in either independent sample's lower work band survive to its actual read. -/
theorem sample_target_before_twenty_one (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (haxes : l.portCount ≤ p.axes)
    (target : List Bool) {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ samples l p)
    (hy : q.2.val = p.H - readDepth p 1 ∨ q.2.val = p.H - (readDepth p 1 + 2))
    (htarget : q ∈ targetHoles l p target) :
    q ∈ (emit ((schedule l p (targetHoles l p target \ Boundary.frame).card).take 21)
      (targetHoles l p target)).remaining := by
  obtain ⟨marker, hmx, hmy, hm⟩ := actual_sample_marker l p q.1 hx
  have hm := newCentralMarkers_subset l p hm
  have hnotaxis : q.1.val ∉ axes l p := by
    rw [← hmx]
    exact sample_not_axes l p hm hmy
  have hnotcore : q.1.val ∉ cores l p := fun hc => hnotaxis (l.acceptanceCore_subset_axes p hl hc)
  have hnotguard : q.1.val ∉ guards l p := by
    rw [← hmx]
    exact sample_not_guards l p hl hm hmy
  have hlower (a : PageColumn) (ha : a ∈ pageColumns l p .lower) : q.1.val ≠ a.column := by
    rw [← hmx]
    exact sample_not_lower_column l p hl haxes hm hmy ha
  have hnotprivate : q.1.val ∉ privateColumns l p := by
    intro hc
    obtain ⟨a, ha, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact hlower a (List.mem_filter.mp ha).1 he.symm
  have hY := readDepth_ge p le_rfl p.levels_pos
  have hD := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hyband : p.D + 32 < q.2.val ∧ q.2.val < p.H := by omega
  have htrimL : ReadAvoids q (trimRound l p .lower) := by
    intro hread
    obtain ⟨a, ha, _, hcol, _⟩ := (mem_trim_region l p .lower q).mp hread
    exact hlower a ha hcol
  have htrimU : ReadAvoids q (trimRound l p .upper) := by
    intro hread
    have hd := trim_depth_bound l p hl hM .upper hread
    simp only [pageDepth, ite_true] at hd
    omega
  have hmain (side : Side) : ReadAvoids q (mainRound l p side) := by
    intro hread
    cases side <;> obtain ⟨_, hreq, hcol, _⟩ := (mem_readRegion _ _ q).mp hread
    all_goals
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp hreq
      apply hnotaxis
      apply List.mem_toFinset.mpr
      exact List.mem_map.mpr ⟨e.port, List.mem_range.mpr (l.endpoints_port_lt hl (List.mem_filter.mp he).1), hcol.symm⟩
  have hprivate : ReadAvoids q (privateRound l p) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnotprivate
  have hguardN : ReadAvoids q (.read .north (prefixRequests (guards l p) fun _ => p.D - 4)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnotguard
  have hguardS : ReadAvoids q (readColumns p .south (guards l p)) :=
    avoid_prefix_columns .south (Or.inr rfl) _ _ hnotguard
  have haxis : ReadAvoids q (axisReadRound l p) := by
    intro hread
    change q ∈ readRegion .north (_ ++ _) at hread
    rw [readRegion_append] at hread
    exact (Finset.mem_union.mp hread).elim
      (avoid_prefix_columns .north (Or.inl rfl) _ _ (fun hc => hnotaxis (Finset.mem_sdiff.mp hc).1))
      (avoid_prefix_columns .north (Or.inl rfl) _ _ hnotcore)
  have hcore : ReadAvoids q (.read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1)) :=
    avoid_prefix_columns .north (Or.inl rfl) _ _ hnotcore
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
    intro hread
    obtain ⟨e, he, hrow⟩ := List.mem_map.mp (List.mem_toFinset.mp hread)
    obtain ⟨hej, hem⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
    have hb := readDepth_add_lt_D p e.level
    rw [readDepth_eq p hej hem] at hb
    omega
  have hframe : ∀ stage ∈ frameSchedule p.W p.H, ReadAvoids q stage := by
    apply frame_avoids p
    intro hf
    obtain ⟨middle, _, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hx)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    obtain ⟨d, hd⟩ := (Boundary.mem_frame q).mp hf
    cases d <;> simp only [Boundary.edge, Finset.mem_filter, Finset.mem_univ, true_and] at hd
    · omega
    · have he : q.1.val = p.x p.axes := by change q.1.val = p.W; omega
      exact hx.elim (fun hx => sample_off_axis p middle p.axes (offset := 2) (by omega) (hx.symm.trans he))
        (fun hx => sample_off_axis p middle p.axes (offset := 10) (by omega) (hx.symm.trans he))
    · omega
    · have hxm := readLength_add_lt_x p middle 0
      omega
  have hclear : ∀ side cols, ReadAvoids q (.clear side cols) := fun _ _ => trivial
  apply emit_mem_of_no_reads _ _ (take_discarded_zero l p hl hM haxes target 21) htarget
  have hprefix : (schedule l p (targetHoles l p target \ Boundary.frame).card).take 21 =
      preparation l p (targetHoles l p target \ Boundary.frame).card ++
      [readRows p .west (probeRows l p), .clear .east (probeRows l p), axisReadRound l p,
        .clear .north (axes l p \ cores l p),
        .clear .west (Finset.range (p.H + 1) \ (workRows l p ∪ cutRows p ∪ {p.D + 4})),
        .read .north (prefixRequests (cores l p) fun _ => p.H - p.Y 1 + 1),
        readColumns p .south (guards l p), .clear .north (guards l p)] := by
    simp only [schedule, preparation, frameSchedule, axisReadRound]
    simp only [List.cons_append, List.nil_append, List.take_succ_cons, List.take_zero]
  have hall : ∀ stage ∈ (schedule l p (targetHoles l p target \ Boundary.frame).card).take 21, ReadAvoids q stage := by
    rw [hprefix]
    rw [preparation_eq_secondRows]
    simp only [secondRowSchedule, mainAxisSchedule, firstRowSchedule, firstTrimSchedule, markerPreparation]
    simp only [List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil, forall_false]
    simp only [hclear, htrimL, htrimU, hmain, hprivate, hguardN, hguardS, haxis, hcore]
    simp only [hflanks, hminus, hprobe, true_and]
    repeat' apply And.intro
    all_goals first | exact hframe | exact fun _ => trivial
  exact fun side requests h => hall (.read side requests) h

end PushPuzzle.Push.AcceptanceProgram

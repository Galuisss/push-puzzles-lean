/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramLower
public import PushS.PortInventorySum
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramFrame
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramLower
import all Push.AcceptanceProgram

/-! The complete actual multilevel acceptance program is lossless and pays for every target hole. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

private theorem upper_marker_live (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hm : InterlevelMarker l p .upper q) : q.1.val ∈ live l p .upper := by
  obtain ⟨a, ha, hj, hjm, hx, _⟩ := hm
  apply List.mem_toFinset.mpr
  apply List.mem_map.mpr
  exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa using And.intro hj hjm⟩, hx.symm⟩

private theorem upper_initial_clear_empty (l : PortLayout) (p : Scales.Parameters)
    (E : Finset (Cell (p.W + 1) (p.H + 1)))
    (hs : ∀ q ∈ E, InterlevelMarker l p .upper q) :
    (E.filter fun q => Direction.north.lane q ∈ auxiliaries l p \ live l p .upper) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  exact (Finset.mem_sdiff.mp hx).2 (upper_marker_live l p (hs q hq))

private theorem upper_pair_clear_empty (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (j : ℕ)
    (hs : ∀ q ∈ E, InterlevelMarker l p .upper q) :
    ((emit [readRows p .west {(p.Y j + p.Y (j + 1)) / 2}] E).remaining.filter fun q =>
      Direction.north.lane q ∈ levelColumns l p .upper j) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hx⟩ := Finset.mem_filter.mp hq
  change q.1.val ∈ levelColumns l p .upper j at hx
  obtain ⟨a, ha, hj, hjm, hxa, hy⟩ := hs q (emit_remaining_subset _ _ hq)
  obtain ⟨b, hb, hxb⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨hb, hbj⟩ := List.mem_filter.mp hb
  have hbj : b.level = j := by simpa using hbj
  have hlevel := l.acceptanceUpperColumn_level p hl ha hb (hxa.symm.trans hxb.symm)
  have haj : a.level = j := hlevel.trans hbj
  rw [pageDepth, ite_eq_left rfl, trimDepth, ite_eq_left hjm, haj] at hy
  have hread : readRows p .west {(p.Y j + p.Y (j + 1)) / 2} ∈
      [readRows p .west {(p.Y j + p.Y (j + 1)) / 2}] := .head _
  exact emit_stage_excluded hread hq
    ((readRows_region p .west _ (Or.inl rfl) q).mpr (Finset.mem_singleton.mpr hy))

private theorem upper_pair_discarded_zero (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (j : ℕ)
    (hs : ∀ q ∈ E, InterlevelMarker l p .upper q) :
    (emit [readRows p .west {(p.Y j + p.Y (j + 1)) / 2}, .clear .north (levelColumns l p .upper j)] E).discarded = 0 := by
  have hh := upper_pair_clear_empty l p hl E j hs
  simp only [readRows, emit, Nat.add_zero] at hh ⊢
  rw [hh, Finset.card_empty]

private theorem upper_layers_discarded_zero (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (levels : List ℕ) (E : Finset (Cell (p.W + 1) (p.H + 1)))
    (hs : ∀ q ∈ E, InterlevelMarker l p .upper q) :
    (emit (levels.flatMap fun j => [readRows p .west {(p.Y (j + 1) + p.Y (j + 1 + 1)) / 2},
      .clear .north (levelColumns l p .upper (j + 1))]) E).discarded = 0 := by
  induction levels generalizing E with
  | nil => rfl
  | cons j levels ih =>
    rw [List.flatMap_cons, emit_discarded_append, upper_pair_discarded_zero l p hl E (j + 1) hs, Nat.zero_add]
    exact ih _ (fun q hq => hs q (emit_remaining_subset _ _ hq))

/-- Every upper-page clear is lossless on the actual stock of remaining upper interlevel markers. -/
private theorem upper_discarded_zero (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (E : Finset (Cell (p.W + 1) (p.H + 1))) (hs : ∀ q ∈ E, InterlevelMarker l p .upper q) :
    (emit (pageChecks l p .upper) E).discarded = 0 := by
  rw [pageChecks, ite_eq_right (by decide : Side.upper ≠ .lower), emit_discarded_append]
  have hclear : (emit [Template.clear .north (auxiliaries l p \ live l p .upper)] E).discarded = 0 := by
    simp only [emit, Nat.add_zero]
    rw [upper_initial_clear_empty l p E hs, Finset.card_empty]
  rw [hclear, Nat.zero_add]
  simp only [ite_eq_right (by decide : Side.upper ≠ .lower)]
  exact upper_layers_discarded_zero l p hl _ _ (fun q hq => hs q (emit_remaining_subset _ _ hq))

/-- The literal complete schedule splits into its complete lower prefix and its upper checks. -/
theorem schedule_eq_lower_upper (l : PortLayout) (p : Scales.Parameters) (k : ℕ) :
    schedule l p k = lowerSchedule l p k ++ pageChecks l p .upper := by
  simp only [schedule, lowerSchedule, workSchedule, workReadSchedule, thirdRowSchedule, axisSchedule,
    axisTail, workTail, axisReadRound, thirdRowKeep, List.append_assoc, List.cons_append, List.nil_append]

/-- No clear in the complete real marked-target program deletes a hole. -/
theorem schedule_discarded_zero (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    (emit (schedule l p (targetHoles l p target \ Boundary.frame).card)
      (targetHoles l p target)).discarded = 0 := by
  rw [schedule_eq_lower_upper, emit_discarded_append, lower_discarded_zero l p hl hM ha target, Nat.zero_add]
  exact upper_discarded_zero l p hl _ (fun q hq => lower_remaining_inventory l p hl hM ha target hq)

/-- Every canonical target hole is paid for by the actual program's positive read quotas. -/
theorem program_full_quota (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (target : List Bool) :
    Scan.quota (instructions (w := p.W + 1) (h := p.H + 1) (program l p target).rounds) =
      (targetHoles l p target).card := by
  have haccount := program_accounting l p target
  have hz : (program l p target).discarded = 0 := schedule_discarded_zero l p hl hM ha target
  simpa only [hz, Nat.add_zero] using haccount

/-- The actual target program's read quotas equal the actual canonical source's hole inventory. -/
theorem program_source_quota (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (initial target : List Bool) :
    Scan.quota (instructions (w := p.W + 1) (h := p.H + 1) (program l p target).rounds) =
      (SegmentRecipe.holes (p.W + 1) (p.H + 1) (l.encodedSegments p (l.canonical initial))).card := by
  rw [program_full_quota l p hl hM ha target, targetHoles]
  exact (l.encodedSegments_holes_card_eq p hl hM ha (l.canonical initial) (l.canonical target)).symm

end PushPuzzle.Push.AcceptanceProgram

/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramRounds

/-! Coordinate regions characterize every actual clear loss of the static target emitter. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS

variable {w h : ℕ}

/-- All literal coordinate prefixes read in one whole round. -/
def readRegion (side : Direction) : List (ℕ × ℕ) → Finset (Cell w h)
  | [] => ∅
  | (lane, span) :: requests =>
      ((Scan.lineCells side lane).take span).toFinset ∪ readRegion side requests

/-- The board cells touched by a round, irrespective of their current occupancy. -/
def Template.region : Template → Finset (Cell w h)
  | .read side requests => readRegion side requests
  | .clear side lanes => Finset.univ.filter fun p => side.lane p ∈ lanes

/-- Every coordinate removed by any round of the schedule. -/
def allRegions : List Template → Finset (Cell w h)
  | [] => ∅
  | stage :: schedule => stage.region ∪ allRegions schedule

/-- Target reads remove the exact union of their requested coordinate prefixes. -/
theorem emitReads_remaining (side : Direction) (requests : List (ℕ × ℕ)) (E : Finset (Cell w h)) :
    (emitReads side requests E).remaining = E \ readRegion side requests := by
  induction requests generalizing E with
  | nil => simp only [emitReads, readRegion, Finset.sdiff_empty]
  | cons request requests ih =>
    rcases request with ⟨lane, span⟩
    simp only [emitReads, ih, readRegion]
    ext p
    simp only [Finset.mem_sdiff, Finset.mem_union]
    tauto

private theorem clear_remaining (side : Direction) (lanes : Finset ℕ) (E : Finset (Cell w h)) :
    E.filter (fun p => side.lane p ∉ lanes) = E \ (Template.clear side lanes).region := by
  ext p
  simp only [Template.region, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_univ, true_and]

/-- The emitted target residual is a direct set difference against the static coordinate schedule. -/
theorem emit_remaining (schedule : List Template) (E : Finset (Cell w h)) :
    (emit schedule E).remaining = E \ allRegions schedule := by
  induction schedule generalizing E with
  | nil => simp only [emit, allRegions, Finset.sdiff_empty]
  | cons stage schedule ih =>
    cases stage with
    | read side requests =>
      simp only [emit, ih, emitReads_remaining, allRegions, Template.region]
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto
    | clear side lanes =>
      simp only [emit, ih, clear_remaining, allRegions]
      ext p
      simp only [Finset.mem_sdiff, Finset.mem_union]
      tauto

/-- The static touched region is exactly the union of the scheduled block regions. -/
theorem mem_allRegions (schedule : List Template) (q : Cell w h) :
    q ∈ allRegions schedule ↔ ∃ stage ∈ schedule, q ∈ stage.region := by
  induction schedule with
  | nil => simp only [allRegions, Finset.notMem_empty, List.not_mem_nil, false_and, exists_false]
  | cons stage schedule ih => simp only [allRegions, Finset.mem_union, ih,
      List.mem_cons, exists_eq_or_imp]

/-- A final target hole has not been touched by any earlier read or clear block. -/
theorem emit_stage_excluded {schedule : List Template} {E : Finset (Cell w h)}
    {stage : Template} (hstage : stage ∈ schedule) {q : Cell w h}
    (hq : q ∈ (emit schedule E).remaining) : q ∉ stage.region := by
  rw [emit_remaining] at hq
  intro ht
  exact (Finset.mem_sdiff.mp hq).2 ((mem_allRegions schedule q).mpr ⟨stage, hstage, ht⟩)

/-- Prefix regions compose by union within a same-direction block. -/
theorem readRegion_append (side : Direction) (left right : List (ℕ × ℕ)) :
    readRegion (w := w) (h := h) side (left ++ right) = readRegion side left ∪ readRegion side right := by
  induction left with
  | nil => exact (Finset.empty_union _).symm
  | cons request left ih =>
    rcases request with ⟨lane, span⟩
    simp only [List.cons_append, readRegion, ih, Finset.union_assoc]

/-- A clear encounters no current hole once its entire region was touched by the preceding schedule. -/
theorem clear_empty_of_touched (before : List Template) (E : Finset (Cell w h))
    (side : Direction) (lanes : Finset ℕ)
    (hcover : (Template.clear side lanes).region ⊆ allRegions (w := w) (h := h) before) :
    ((emit before E).remaining.filter fun q => side.lane q ∈ lanes) = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro q hq
  obtain ⟨hq, hline⟩ := Finset.mem_filter.mp hq
  rw [emit_remaining] at hq
  apply (Finset.mem_sdiff.mp hq).2
  exact hcover (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hline⟩)

end PushPuzzle.Push.AcceptanceProgram

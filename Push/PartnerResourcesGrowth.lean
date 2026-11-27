/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesCuts

/-! Polynomial finite inventory growth of the actual repair program on every raw input. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS

private theorem bufferAt_upper_count (s : BufferState) (first : ℕ) :
    (s.bufferAt first).layout.upperPairs.length ≤ s.layout.upperPairs.length + 1 := by
  unfold BufferState.bufferAt
  split_ifs with hg hl hr
  · simp only [BufferState.insertEar, ear, List.length_cons, List.length_map, List.length_erase_of_mem hl]
    have := List.length_pos_of_mem hl
    omega
  · simp only [BufferState.insertEar, ear, List.length_cons, List.length_map, List.length_erase_of_mem hr]
    have := List.length_pos_of_mem hr
    omega
  all_goals omega

private theorem bufferAt_lower_count (s : BufferState) (first : ℕ) :
    (s.bufferAt first).layout.lowerGroups.length ≤ s.layout.lowerGroups.length + 1 := by
  unfold BufferState.bufferAt
  split_ifs <;> (try simp only [BufferState.insertEar, ear, List.length_append, List.length_map,
    List.length_singleton]) <;> omega

theorem internal_scan_counts (s : BufferState) (positions : List ℕ) :
    (s.scan positions).layout.upperPairs.length ≤ s.layout.upperPairs.length + positions.length ∧
      (s.scan positions).layout.lowerGroups.length ≤ s.layout.lowerGroups.length + positions.length := by
  induction positions generalizing s with
  | nil => exact ⟨le_rfl, le_rfl⟩
  | cons first rest ih =>
    have h := ih (s.bufferAt first)
    have hu := bufferAt_upper_count s first
    have hl := bufferAt_lower_count s first
    change (s.bufferAt first |>.scan rest).layout.upperPairs.length ≤ _ ∧
      (s.bufferAt first |>.scan rest).layout.lowerGroups.length ≤ _
    simp only [List.length_cons]
    omega

private theorem upperPieces_length (xs : List ((ℕ × ℕ) × ℕ)) (cut count : ℕ) :
    (xs.flatMap (Cuts.upperPiece cut count)).length = 2 * xs.length := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp only [List.flatMap_cons, List.length_append, Cuts.upperPiece,
      List.length_cons, List.length_nil, ih]; omega

private theorem cut_upper_count (l : PortLayout) (cut : ℕ) :
    (Cuts.compile l cut).upperPairs.length = l.upperPairs.length + (Cuts.active l cut).length := by
  have h := (Cuts.active_passive_perm l cut).length_eq
  simp only [List.length_append] at h
  simp only [Cuts.compile, List.length_append, upperPieces_length, List.length_map, List.length_zipIdx]
  omega

private theorem cut_lower_count (l : PortLayout) (cut : ℕ) :
    (Cuts.compile l cut).lowerGroups.length = l.lowerGroups.length + (Cuts.active l cut).length := by
  simp only [Cuts.compile, List.length_append, List.length_map, List.length_zipIdx]

theorem cut_active_le_of_load {l : PortLayout} {bound : ℕ} (hload : ∀ gap, upperLoad l gap ≤ bound) (cut : ℕ) :
    (Cuts.active l cut).length ≤ bound := by
  by_cases hc : 0 < cut
  · rw [cut_active_length l hc]
    exact hload _
  · have he : cut = 0 := by omega
    rw [he, cut_active_zero]
    exact Nat.zero_le _

private theorem cutAt_load_le (s : BufferState) {bound : ℕ} (hload : ∀ gap, upperLoad s.layout gap ≤ bound)
    (cut gap : ℕ) : upperLoad (Cuts.cutAt s cut).layout gap ≤ bound := by
  unfold Cuts.cutAt
  split_ifs
  · exact cut_upperLoad_le hload cut gap
  · exact hload gap

private theorem cutAt_counts (s : BufferState) {bound : ℕ} (hload : ∀ gap, upperLoad s.layout gap ≤ bound) (cut : ℕ) :
    (Cuts.cutAt s cut).layout.portCount ≤ s.layout.portCount + 2 * bound ∧
    (Cuts.cutAt s cut).layout.upperPairs.length ≤ s.layout.upperPairs.length + bound ∧
      (Cuts.cutAt s cut).layout.lowerGroups.length ≤ s.layout.lowerGroups.length + bound := by
  have ht := cut_active_le_of_load hload cut
  unfold Cuts.cutAt
  split_ifs
  · rw [cut_upper_count, cut_lower_count]
    change s.layout.portCount + 2 * _ ≤ _ ∧ _
    omega
  · omega

/-- All reachable common-cut fold accumulators have polynomially bounded finite inventories on arbitrary raw inputs. -/
theorem cut_scan_counts (s : BufferState) (positions : List ℕ) {bound : ℕ}
    (hload : ∀ gap, upperLoad s.layout gap ≤ bound) :
    (Cuts.scan s positions).layout.portCount ≤ s.layout.portCount + 2 * bound * positions.length ∧
    (Cuts.scan s positions).layout.upperPairs.length ≤ s.layout.upperPairs.length + bound * positions.length ∧
      (Cuts.scan s positions).layout.lowerGroups.length ≤ s.layout.lowerGroups.length + bound * positions.length := by
  induction positions generalizing s with
  | nil => simp only [Cuts.scan, List.foldl_nil, List.length_nil, Nat.mul_zero, Nat.add_zero, le_refl, and_self]
  | cons cut rest ih =>
    have h := ih (Cuts.cutAt s cut) (fun gap => cutAt_load_le s hload cut gap)
    have hstep := cutAt_counts s hload cut
    change (Cuts.scan (Cuts.cutAt s cut) rest).layout.portCount ≤ _ ∧
      (Cuts.scan (Cuts.cutAt s cut) rest).layout.upperPairs.length ≤ _ ∧
      (Cuts.scan (Cuts.cutAt s cut) rest).layout.lowerGroups.length ≤ _
    simp only [List.length_cons]
    exact ⟨by nlinarith [h.1, hstep.1], by nlinarith [h.2.1, hstep.2.1], by nlinarith [h.2.2, hstep.2.2]⟩

end PushPuzzle.Push.Partner.Resources

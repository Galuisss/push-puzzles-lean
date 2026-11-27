/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerResourcesGrowth
import all Push.PartnerInternal

/-! Unary numerical labels remain polynomially bounded throughout the actual repair folds. -/

@[expose] public section
namespace PushPuzzle.Push.Partner.Resources

open PushS

/-- Bounds on every actual numerical layout field, including all three incidences of each gate. -/
structure LabelsBounded (l : PortLayout) (bound : ℕ) : Prop where
  portCount : l.portCount ≤ bound
  upper (a b : ℕ) : (a, b) ∈ l.upperPairs → a ≤ bound ∧ b ≤ bound
  lower_wire (a b : ℕ) : LowerGroup.wire a b ∈ l.lowerGroups → a ≤ bound ∧ b ≤ bound
  lower_gate (kind : Shuttle.Kind) (first : ℕ) : LowerGroup.gate kind first ∈ l.lowerGroups → first + 2 ≤ bound

theorem LabelsBounded.mono {l : PortLayout} {a b : ℕ} (h : LabelsBounded l a) (hab : a ≤ b) : LabelsBounded l b := by
  refine ⟨h.portCount.trans hab, ?_, ?_, ?_⟩
  · intro x y hm
    exact ⟨(h.upper x y hm).1.trans hab, (h.upper x y hm).2.trans hab⟩
  · intro x y hm
    exact ⟨(h.lower_wire x y hm).1.trans hab, (h.lower_wire x y hm).2.trans hab⟩
  · intro kind first hm
    exact (h.lower_gate kind first hm).trans hab

private theorem ear_shift_le (cut i : ℕ) : shift cut i ≤ i + 2 := by unfold shift; split_ifs <;> omega
private theorem cut_shift_le (cut count i : ℕ) : Cuts.shift cut count i ≤ i + 2 * count := by
  unfold Cuts.shift
  split_ifs <;> omega

private theorem ear_labels {l : PortLayout} {bound cut : ℕ} {ab : ℕ × ℕ}
    (hl : LabelsBounded l bound) (hp : ab ∈ l.upperPairs) (hc : cut + 1 ≤ bound + 2) :
    LabelsBounded (ear l cut ab) (bound + 2) := by
  have ha := hl.upper ab.1 ab.2 hp
  have hs₁ := ear_shift_le cut ab.1
  have hs₂ := ear_shift_le cut ab.2
  have hn := hl.portCount
  refine ⟨by change l.portCount + 2 ≤ _; omega, ?_, ?_, ?_⟩
  · intro a b hm
    simp only [ear, List.mem_cons] at hm
    rcases hm with he | he | hold
    · cases he
      exact ⟨(Nat.min_le_left _ _).trans (by omega), max_le (by omega) hc⟩
    · cases he
      exact ⟨(Nat.min_le_left _ _).trans (by omega), max_le (by omega) (by omega)⟩
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases he
      have hb := hl.upper old.1 old.2 (List.mem_of_mem_erase hmem)
      have hs₁ := ear_shift_le cut old.1
      have hs₂ := ear_shift_le cut old.2
      exact ⟨by omega, by omega⟩
  · intro a b hm
    rcases List.mem_append.mp hm with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | gate kind first => cases he
      | wire x y =>
        simp only [mapGroup, LowerGroup.wire.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hb := hl.lower_wire x y hmem
        have hs₁ := ear_shift_le cut x
        have hs₂ := ear_shift_le cut y
        exact ⟨by omega, by omega⟩
    · cases List.mem_singleton.mp hnew
      exact ⟨by omega, hc⟩
  · intro kind first hm
    rcases List.mem_append.mp hm with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | wire x y => cases he
      | gate other f =>
        simp only [mapGroup, LowerGroup.gate.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hb := hl.lower_gate other f hmem
        have hs := ear_shift_le cut f
        omega
    · cases List.mem_singleton.mp hnew

private theorem bufferAt_labels (s : BufferState) (first : ℕ) {bound : ℕ}
    (hl : LabelsBounded s.layout bound) :
    LabelsBounded (s.bufferAt first).layout (bound + 2) := by
  unfold BufferState.bufferAt
  split_ifs with hg ha hb
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    have hc := hl.lower_gate kind first hgate
    exact ear_labels hl ha (by omega)
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    have hc := hl.lower_gate kind first hgate
    exact ear_labels hl hb (by omega)
  all_goals exact hl.mono (by omega)

private theorem bufferAt_positions (s : BufferState) (first : ℕ) {bound : ℕ}
    (hp : ∀ i ∈ s.ports, i ≤ bound) :
    ∀ i ∈ (s.bufferAt first).ports, i ≤ bound + 2 := by
  unfold BufferState.bufferAt
  split_ifs
  · intro i hi
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
    exact (ear_shift_le first old).trans (Nat.add_le_add_right (hp old hold) 2)
  · intro i hi
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
    exact (ear_shift_le (first + 3) old).trans (Nat.add_le_add_right (hp old hold) 2)
  all_goals intro i hi; have := hp i hi; omega

theorem internal_scan_labels (s : BufferState) (positions : List ℕ) {bound : ℕ} (hl : LabelsBounded s.layout bound) :
    LabelsBounded (s.scan positions).layout (bound + 2 * positions.length) := by
  induction positions generalizing s bound with
  | nil => exact hl
  | cons first rest ih =>
    have h := ih (s.bufferAt first) (bufferAt_labels s first hl)
    simpa only [BufferState.scan, List.foldl_cons, List.length_cons, Nat.mul_add, Nat.mul_one,
      Nat.add_assoc, Nat.add_comm 2] using h

theorem internal_scan_positions (s : BufferState) (positions : List ℕ) {bound : ℕ}
    (hp : ∀ i ∈ s.ports, i ≤ bound) : ∀ i ∈ (s.scan positions).ports, i ≤ bound + 2 * positions.length := by
  induction positions generalizing s bound with
  | nil => exact hp
  | cons first rest ih =>
    intro i hi
    have h := ih (s.bufferAt first) (bufferAt_positions s first hp) i hi
    simp only [List.length_cons]
    omega

/-- A common-cut block shifts old numerical labels and introduces fresh labels by exactly its finite span. -/
private theorem cut_labels {l : PortLayout} {bound : ℕ} (hl : LabelsBounded l bound) (cut : ℕ) :
    LabelsBounded (Cuts.compile l cut) (bound + 2 * (Cuts.active l cut).length) := by
  have hn := hl.portCount
  refine ⟨by change l.portCount + 2 * _ ≤ _; omega, ?_, ?_, ?_⟩
  · intro a b hab
    rcases List.mem_append.mp hab with hnew | hold
    · obtain ⟨p, hp, hmem⟩ := List.mem_flatMap.mp hnew
      obtain ⟨hm, _, hpc⟩ := (Cuts.mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
      have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      have hraw := hl.upper p.1.1 p.1.2 hm
      have hleft := Cuts.left_bounds (cut := cut) hj
      have hright := Cuts.right_bounds (cut := cut) hj
      have hs₁ := cut_shift_le cut (Cuts.active l cut).length p.1.1
      have hs₂ := cut_shift_le cut (Cuts.active l cut).length p.1.2
      simp only [Cuts.upperPiece, List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with he | he
      · cases he
        exact ⟨by omega, by omega⟩
      · cases he
        exact ⟨by omega, by omega⟩
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases he
      have hb := hl.upper old.1 old.2 ((Cuts.mem_passive l cut old).mp hmem).1
      have hs₁ := cut_shift_le cut (Cuts.active l cut).length old.1
      have hs₂ := cut_shift_le cut (Cuts.active l cut).length old.2
      exact ⟨by omega, by omega⟩
  · intro a b hab
    rcases List.mem_append.mp hab with hold | hnew
    · obtain ⟨old, hmem, he⟩ := List.mem_map.mp hold
      cases old with
      | gate kind first => cases he
      | wire x y =>
        simp only [Cuts.mapGroup, LowerGroup.wire.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        have hb := hl.lower_wire x y hmem
        have hs₁ := cut_shift_le cut (Cuts.active l cut).length x
        have hs₂ := cut_shift_le cut (Cuts.active l cut).length y
        exact ⟨by omega, by omega⟩
    · obtain ⟨p, hp, he⟩ := List.mem_map.mp hnew
      cases he
      obtain ⟨hm, _, hpc⟩ := (Cuts.mem_active l cut _).mp (List.fst_mem_of_mem_zipIdx hp)
      have hraw := hl.upper p.1.1 p.1.2 hm
      have hj : p.2 < (Cuts.active l cut).length := by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx hp
      have hleft := Cuts.left_bounds (cut := cut) hj
      have hright := Cuts.right_bounds (cut := cut) hj
      exact ⟨by omega, by omega⟩
  · intro kind first hg
    obtain ⟨old, hold, rfl⟩ := (Cuts.compile_gate_mem l cut kind first).mp hg
    have hb := hl.lower_gate kind old hold
    have hs := cut_shift_le cut (Cuts.active l cut).length old
    omega

private theorem cutAt_labels (s : BufferState) (cut : ℕ) {bound load : ℕ}
    (hl : LabelsBounded s.layout bound) (hu : ∀ gap, upperLoad s.layout gap ≤ load) :
    LabelsBounded (Cuts.cutAt s cut).layout (bound + 2 * load) := by
  have ht := cut_active_le_of_load hu cut
  unfold Cuts.cutAt
  split_ifs
  · exact (cut_labels hl cut).mono (by omega)
  · exact hl.mono (by omega)

private theorem cutAt_positions (s : BufferState) (cut : ℕ) {bound load : ℕ}
    (hp : ∀ i ∈ s.ports, i ≤ bound) (hu : ∀ gap, upperLoad s.layout gap ≤ load) :
    ∀ i ∈ (Cuts.cutAt s cut).ports, i ≤ bound + 2 * load := by
  have ht := cut_active_le_of_load hu cut
  unfold Cuts.cutAt
  split_ifs
  · intro i hi
    obtain ⟨old, hold, rfl⟩ := List.mem_map.mp hi
    have hs := cut_shift_le cut (Cuts.active s.layout cut).length old
    have := hp old hold
    omega
  · intro i hi
    have := hp i hi
    omega

theorem cut_scan_labels (s : BufferState) (positions : List ℕ) {bound load : ℕ}
    (hl : LabelsBounded s.layout bound) (hu : ∀ gap, upperLoad s.layout gap ≤ load) :
    LabelsBounded (Cuts.scan s positions).layout (bound + 2 * load * positions.length) := by
  induction positions generalizing s bound with
  | nil => exact hl
  | cons cut rest ih =>
    have hnext (gap : ℕ) : upperLoad (Cuts.cutAt s cut).layout gap ≤ load := by
      unfold Cuts.cutAt
      split_ifs
      · exact cut_upperLoad_le hu cut gap
      · exact hu gap
    have h := ih (Cuts.cutAt s cut) (cutAt_labels s cut hl hu) hnext
    have he : bound + 2 * load + 2 * load * rest.length = bound + 2 * load * (cut :: rest).length := by
      simp only [List.length_cons]; ring
    simpa only [Cuts.scan, List.foldl_cons, he] using h

theorem cut_scan_positions (s : BufferState) (positions : List ℕ) {bound load : ℕ}
    (hp : ∀ i ∈ s.ports, i ≤ bound) (hu : ∀ gap, upperLoad s.layout gap ≤ load) :
    ∀ i ∈ (Cuts.scan s positions).ports, i ≤ bound + 2 * load * positions.length := by
  induction positions generalizing s bound with
  | nil => exact hp
  | cons cut rest ih =>
    have hnext (gap : ℕ) : upperLoad (Cuts.cutAt s cut).layout gap ≤ load := by
      unfold Cuts.cutAt
      split_ifs
      · exact cut_upperLoad_le hu cut gap
      · exact hu gap
    intro i hi
    have h := ih (Cuts.cutAt s cut) (cutAt_positions s cut hp hu) hnext i hi
    simp only [List.length_cons]
    nlinarith

end PushPuzzle.Push.Partner.Resources

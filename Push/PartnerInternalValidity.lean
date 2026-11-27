/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.PartnerUpperValidity
import all Push.PartnerInternal
import all Push.PartnerUpperValidity

/-! The actual descending ear compiler preserves valid pages and clears every internal gate pair. -/

@[expose] public section
namespace PushPuzzle.Push.Partner

open PushS

namespace BufferState

theorem bufferAt_valid (s : BufferState) (first : ℕ) (hs : s.layout.pages.Valid) :
    (s.bufferAt first).layout.pages.Valid := by
  unfold bufferAt
  split_ifs with hg hl hr
  · obtain ⟨kind, hgate⟩ := gate_of_any hg
    exact leftEar_valid hs hgate hl
  · obtain ⟨kind, hgate⟩ := gate_of_any hg
    exact rightEar_valid hs hgate hr
  all_goals exact hs

private theorem scan_valid (s : BufferState) (positions : List ℕ) (hs : s.layout.pages.Valid) :
    (s.scan positions).layout.pages.Valid := by
  induction positions generalizing s with
  | nil => exact hs
  | cons first rest ih => exact ih (s.bufferAt first) (s.bufferAt_valid first hs)

end BufferState

/-- The literal internal-pair compiler preserves both standard noncrossing pages. -/
theorem bufferInternal_valid {l : PortLayout} (hl : l.pages.Valid) : (bufferInternal l).layout.pages.Valid :=
  (BufferState.start l).scan_valid _ hl

private theorem mapPair_injective (cut : ℕ) : Function.Injective (mapPair cut) := by
  intro a b he
  apply Prod.ext
  · exact shift_injective cut (congrArg Prod.fst he)
  · exact shift_injective cut (congrArg Prod.snd he)

private theorem mapPair_ne_fresh (cut : ℕ) (xy : ℕ × ℕ) (u fresh : ℕ)
    (hf : ∀ i, shift cut i ≠ fresh) : mapPair cut xy ≠ sortPair u fresh := by
  intro he
  by_cases h : u ≤ fresh
  · have hh := congrArg Prod.snd he
    exact hf xy.2 (by simpa only [mapPair, sortPair, max_eq_right h] using hh)
  · have hh := congrArg Prod.fst he
    exact hf xy.1 (by simpa only [mapPair, sortPair, min_eq_right (by omega : fresh ≤ u)] using hh)

/-- No replacement arc connects two old ports; all surviving old-to-old arcs are exactly the erased list. -/
private theorem ear_old_pair_mem (l : PortLayout) (cut : ℕ) (ab xy : ℕ × ℕ) :
    mapPair cut xy ∈ (ear l cut ab).upperPairs ↔ xy ∈ l.upperPairs.erase ab := by
  simp only [ear, List.mem_cons]
  rw [or_iff_right (mapPair_ne_fresh cut xy _ _ (shift_ne_cut_succ cut)),
    or_iff_right (mapPair_ne_fresh cut xy _ _ (shift_ne_cut cut))]
  simp only [List.mem_map, (mapPair_injective cut).eq_iff, exists_eq_right]

private theorem ear_gate_mem (l : PortLayout) (cut : ℕ) (ab : ℕ × ℕ) (kind : Shuttle.Kind) (first : ℕ) :
    LowerGroup.gate kind first ∈ (ear l cut ab).lowerGroups ↔
      ∃ old, LowerGroup.gate kind old ∈ l.lowerGroups ∧ first = shift cut old := by
  simp only [ear, List.mem_append, List.mem_singleton, List.mem_map]
  constructor
  · rintro (⟨g, hg, he⟩ | he)
    · cases g with
      | wire a b => cases he
      | gate other old =>
        simp only [mapGroup, LowerGroup.gate.injEq] at he
        rcases he with ⟨rfl, rfl⟩
        exact ⟨old, hg, rfl⟩
    · cases he
  · rintro ⟨old, hg, rfl⟩
    exact Or.inl ⟨.gate kind old, hg, rfl⟩

private def ClearAt (l : PortLayout) (first : ℕ) : Prop :=
  (first, first + 1) ∉ l.upperPairs ∧ (first + 1, first + 2) ∉ l.upperPairs

/-- Neither adjacent port pair of a lower gate is an upper pair. -/
def NoInternalPairs (l : PortLayout) : Prop :=
  ∀ kind first, LowerGroup.gate kind first ∈ l.lowerGroups →
    (first, first + 1) ∉ l.upperPairs ∧ (first + 1, first + 2) ∉ l.upperPairs

private theorem ear_clear_preserved {l : PortLayout} {cut : ℕ} {ab : ℕ × ℕ}
    (hs : SafeCut l cut) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hclear : ClearAt l first) :
    ClearAt (ear l cut ab) (shift cut first) := by
  obtain ⟨h₁, h₂⟩ := shift_gate (hs kind first hg)
  constructor
  · intro hm
    have he : (shift cut first, shift cut first + 1) = mapPair cut (first, first + 1) := by
      simp only [mapPair, h₁]
    rw [he, ear_old_pair_mem] at hm
    exact hclear.1 (List.mem_of_mem_erase hm)
  · intro hm
    have he : (shift cut first + 1, shift cut first + 2) = mapPair cut (first + 1, first + 2) := by
      simp only [mapPair, h₁, h₂]
    rw [he, ear_old_pair_mem] at hm
    exact hclear.2 (List.mem_of_mem_erase hm)

private theorem leftEar_clears {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first, first + 1) ∈ l.upperPairs) :
    ClearAt (ear l first (first, first + 1)) (shift first first) := by
  have hn := upperPairs_nodup (inventory_of_pages hl)
  have hright : (first + 1, first + 2) ∉ l.upperPairs := by
    intro hr
    have he := shared_upper (inventory_of_pages hl) hr hp (i := first + 1)
      (by simp [pairPorts]) (by simp [pairPorts])
    have h := congrArg Prod.fst he
    omega
  obtain ⟨h₁, h₂⟩ := shift_gate ((gate_boundary_safe hl hg).1 kind first hg)
  constructor
  · intro hm
    have he : (shift first first, shift first first + 1) = mapPair first (first, first + 1) := by
      simp only [mapPair, h₁]
    rw [he, ear_old_pair_mem] at hm
    exact hn.not_mem_erase hm
  · intro hm
    have he : (shift first first + 1, shift first first + 2) = mapPair first (first + 1, first + 2) := by
      simp only [mapPair, h₁, h₂]
    rw [he, ear_old_pair_mem] at hm
    exact hright (List.mem_of_mem_erase hm)

private theorem rightEar_clears {l : PortLayout} (hl : l.pages.Valid) {kind : Shuttle.Kind} {first : ℕ}
    (hg : LowerGroup.gate kind first ∈ l.lowerGroups) (hp : (first + 1, first + 2) ∈ l.upperPairs) :
    ClearAt (ear l (first + 3) (first + 1, first + 2)) (shift (first + 3) first) := by
  have hn := upperPairs_nodup (inventory_of_pages hl)
  have hleft : (first, first + 1) ∉ l.upperPairs := by
    intro hr
    have he := shared_upper (inventory_of_pages hl) hr hp (i := first + 1)
      (by simp [pairPorts]) (by simp [pairPorts])
    have h := congrArg Prod.fst he
    omega
  obtain ⟨h₁, h₂⟩ := shift_gate ((gate_boundary_safe hl hg).2 kind first hg)
  constructor
  · intro hm
    have he : (shift (first + 3) first, shift (first + 3) first + 1) =
        mapPair (first + 3) (first, first + 1) := by simp only [mapPair, h₁]
    rw [he, ear_old_pair_mem] at hm
    exact hleft (List.mem_of_mem_erase hm)
  · intro hm
    have he : (shift (first + 3) first + 1, shift (first + 3) first + 2) =
        mapPair (first + 3) (first + 1, first + 2) := by simp only [mapPair, h₁, h₂]
    rw [he, ear_old_pair_mem] at hm
    exact hn.not_mem_erase hm

private def ClearedFrom (l : PortLayout) (bound : ℕ) : Prop :=
  ∀ kind first, LowerGroup.gate kind first ∈ l.lowerGroups → bound ≤ first → ClearAt l first

private theorem bufferAt_cleared (s : BufferState) (first : ℕ) (hs : s.layout.pages.Valid)
    (hclear : ClearedFrom s.layout (first + 1)) : ClearedFrom (s.bufferAt first).layout first := by
  unfold BufferState.bufferAt
  split_ifs with hg hl hr
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    intro other start hmem hbound
    obtain ⟨old, hold, rfl⟩ := (ear_gate_mem s.layout first _ other start).mp hmem
    have hge : first ≤ old := by
      unfold shift at hbound
      split_ifs at hbound <;> omega
    by_cases he : old = first
    · subst old
      exact leftEar_clears hs hgate hl
    · exact ear_clear_preserved (gate_boundary_safe hs hgate).1 hold (hclear other old hold (by omega))
  · obtain ⟨kind, hgate⟩ := BufferState.gate_of_any hg
    intro other start hmem hbound
    obtain ⟨old, hold, rfl⟩ := (ear_gate_mem s.layout (first + 3) _ other start).mp hmem
    have hge : first ≤ old := by
      unfold shift at hbound
      split_ifs at hbound <;> omega
    by_cases he : old = first
    · subst old
      exact rightEar_clears hs hgate hr
    · exact ear_clear_preserved (gate_boundary_safe hs hgate).2 hold (hclear other old hold (by omega))
  · intro kind start hmem hbound
    by_cases he : start = first
    · subst start
      exact ⟨hl, hr⟩
    · exact hclear kind start hmem (by omega)
  · intro kind start hmem hbound
    by_cases he : start = first
    · subst start
      apply False.elim
      apply hg
      apply List.any_eq_true.mpr
      exact ⟨_, hmem, by simp⟩
    · exact hclear kind start hmem (by omega)

private theorem scan_range_cleared (s : BufferState) (n : ℕ) (hs : s.layout.pages.Valid)
    (hclear : ClearedFrom s.layout n) :
    ClearedFrom (s.scan (List.range n).reverse).layout 0 := by
  induction n generalizing s with
  | zero => exact hclear
  | succ n ih =>
    have he : (List.range (n + 1)).reverse = n :: (List.range n).reverse := by simp [List.range_succ]
    rw [he]
    exact ih (s.bufferAt n) (s.bufferAt_valid n hs) (bufferAt_cleared s n hs hclear)

/-- Every actual lower gate in the completed ear compiler has no internal upper pair. -/
theorem bufferInternal_no_internal {l : PortLayout} (hl : l.pages.Valid) :
    NoInternalPairs (bufferInternal l).layout := by
  have hstart : ClearedFrom l l.portCount := by
    intro kind first hg hbound
    have := inventory_gate_bound (inventory_of_pages hl) hg
    omega
  have h := scan_range_cleared (BufferState.start l) l.portCount hl hstart
  intro kind first hg
  exact h kind first hg (Nat.zero_le _)

end PushPuzzle.Push.Partner

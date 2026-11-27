/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceSoundnessSupportClean
public import Push.AcceptanceSoundnessSupportCoordinates
import all Push.AcceptanceSoundnessCentralGuard
import all Push.AcceptanceProgramLayout
import all Push.AcceptanceProgramThirdClear
import all Push.AcceptanceProgramWorkClear
import all Push.AcceptanceProgramStock
import all Push.AcceptanceProgramNarrowSignals
import all PushS.PortFixedSeparation
import all PushS.PortSegments

/-! Whole-line ownership of every real read before the non-street column clear. -/

@[expose] public section
namespace PushPuzzle.Push.AcceptanceSoundness

open PushFS PushS PushS.PortLayout AcceptanceProgram

def newMarkerRows (p : Scales.Parameters) : Finset ℕ := {p.D - 2, p.D + 2, p.D - 4, p.D + 4}

private def LaneCover (l : PortLayout) (p : Scales.Parameters) (q : Cell (p.W + 1) (p.H + 1)) : Prop :=
  q ∈ Boundary.frame ∨ q ∈ (supportCoordinates l p).second ∨ q.2.val ∈ newMarkerRows p

private theorem cover_street (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ streetColumns l (coordinates p)) : LaneCover l p q := by
  apply Or.inr ∘ Or.inl
  apply (second_support_iff l p q).mpr ∘ Or.inl
  exact Finset.mem_union_left _ (Finset.mem_union_left _ (List.mem_toFinset.mpr hx))

private theorem cover_guard (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ guards l p) : LaneCover l p q := by
  apply Or.inr ∘ Or.inl
  apply (second_support_iff l p q).mpr ∘ Or.inl
  exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)

private theorem cover_sample (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ samples l p) : LaneCover l p q := by
  apply Or.inr ∘ Or.inl
  apply (second_support_iff l p q).mpr ∘ Or.inl
  exact Finset.mem_union_right _ hx

private theorem cover_work (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hy : q.2.val ∈ workRows l p) : LaneCover l p q :=
  Or.inr (Or.inl ((second_support_iff l p q).mpr (Or.inr hy)))

private theorem prefix_touches (p : Scales.Parameters) (side : Direction) (lanes : Finset ℕ) (span : ℕ → ℕ)
    {q : Cell (p.W + 1) (p.H + 1)}
    (ht : ReadTouches (.read side (prefixRequests lanes span)) q) : side.lane q ∈ lanes := by
  obtain ⟨a, ha, he⟩ := ht
  exact he.symm ▸ ((mem_prefixRequests _ _ _ _).mp ha).1

private theorem row_touches (p : Scales.Parameters) (side : Direction) (rows : Finset ℕ)
    (hs : side = .west ∨ side = .east) {q : Cell (p.W + 1) (p.H + 1)}
    (ht : ReadTouches (readRows p side rows) q) : q.2.val ∈ rows := by
  have h := prefix_touches p side rows _ ht
  rcases hs with rfl | rfl <;> exact h

private theorem axis_cover (l : PortLayout) (p : Scales.Parameters) {q : Cell (p.W + 1) (p.H + 1)}
    (hx : q.1.val ∈ axes l p) : LaneCover l p q := by
  obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  exact cover_street l p (he ▸ axis_in_streetColumns l p (List.mem_range.mp hi))

private theorem trim_cover (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (trimRound l p side) q) : LaneCover l p q := by
  obtain ⟨request, hr, hx⟩ := ht
  obtain ⟨a, ha', he⟩ := List.mem_map.mp hr
  have hstreet := acceptance_column_street l p hl hM ha side (List.mem_filter.mp ha').1
  have hcol : q.1.val = a.column := by cases side <;> simpa only [← he, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
  exact cover_street l p (hcol.symm ▸ hstreet)

private theorem main_cover (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (mainRound l p side) q) : LaneCover l p q := by
  obtain ⟨request, hr, hx⟩ := ht
  obtain ⟨e, he, heq⟩ := List.mem_map.mp hr
  have hstreet := axis_in_streetColumns l p (l.endpoints_port_lt hl (List.mem_filter.mp he).1)
  have hcol : q.1.val = p.x e.port := by cases side <;> simpa only [← heq, Direction.lane, ite_true, reduceCtorEq, ite_false] using hx
  exact cover_street l p (hcol.symm ▸ hstreet)

private theorem private_cover (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches (privateRound l p) q) : LaneCover l p q := by
  have hx := prefix_touches p .south (privateColumns l p) _ ht
  obtain ⟨a, ha', he⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  change a.column = q.1.val at he
  exact cover_street l p (he ▸ acceptance_column_street l p hl hM ha .lower (List.mem_filter.mp ha').1)

private theorem probe_cover (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) {q : Cell (p.W + 1) (p.H + 1)}
    (ht : ReadTouches (readRows p .west (probeRows l p)) q) : LaneCover l p q := by
  obtain ⟨e, he, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp (row_touches p .west _ (Or.inl rfl) ht))
  have hj := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
  exact cover_work l p (heq ▸ (level_work_rows l p .upper hj.1 hj.2).2)

/-- All first twenty-four actual read lines lie on the second support or the four separately protected new rows. -/
theorem early_read_lane_cover (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (k : ℕ)
    {stage : Template} (hstage : stage ∈ workReadSchedule l p k)
    {q : Cell (p.W + 1) (p.H + 1)} (ht : ReadTouches stage q) :
    q ∈ Boundary.frame ∨ q ∈ (supportCoordinates l p).second ∨ q.2.val ∈ newMarkerRows p := by
  simp only [workReadSchedule, thirdRowSchedule, axisSchedule, axisTail, workTail, preparation,
    frameSchedule, List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hstage
  rcases hstage with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · obtain ⟨a, ha', hx⟩ := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    have hx' : q.1.val = 0 ∨ q.1.val = p.W := by
      rcases ha' with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    apply Or.inl
    rcases hx' with hx' | hx'
    · exact (Boundary.mem_frame q).mpr ⟨.west, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hx'⟩⟩
    · exact (Boundary.mem_frame q).mpr ⟨.east, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  · obtain ⟨a, ha', hx⟩ := ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
    have hy : q.2.val = 0 ∨ q.2.val = p.H := by
      rcases ha' with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
    apply Or.inl
    rcases hy with hy | hy
    · exact (Boundary.mem_frame q).mpr ⟨.north, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hy⟩⟩
    · exact (Boundary.mem_frame q).mpr ⟨.south, Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩⟩
  · exact ht.elim
  · exact trim_cover l p hl hM ha .lower ht
  · exact trim_cover l p hl hM ha .upper ht
  · exact ht.elim
  · exact main_cover l p hl .upper ht
  · exact main_cover l p hl .lower ht
  · exact ht.elim
  · exact private_cover l p hl hM ha ht
  · apply Or.inr ∘ Or.inr
    have hy := row_touches p .east _ (Or.inr rfl) ht
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto
  · exact cover_guard l p (prefix_touches p .north _ _ ht)
  · apply Or.inr ∘ Or.inr
    have hy := row_touches p .west _ (Or.inl rfl) ht
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto
  · exact probe_cover l p hl hM ht
  · exact ht.elim
  · obtain ⟨a, ha', hx⟩ := ht
    change q.1.val = a.1 at hx
    rcases List.mem_append.mp ha' with ha' | ha'
    · exact axis_cover l p (hx.symm ▸ (Finset.mem_sdiff.mp ((mem_prefixRequests _ _ _ _).mp ha').1).1)
    · exact axis_cover l p (hx.symm ▸ l.acceptanceCore_subset_axes p hl ((mem_prefixRequests _ _ _ _).mp ha').1)
  · exact ht.elim
  · exact ht.elim
  · exact axis_cover l p (l.acceptanceCore_subset_axes p hl (prefix_touches p .north _ _ ht))
  · exact cover_guard l p (prefix_touches p .south _ _ ht)
  · exact ht.elim
  · exact cover_sample l p (prefix_touches p .south _ _ ht)
  · apply Or.inr ∘ Or.inr
    have hy := row_touches p .east _ (Or.inr rfl) ht
    simp only [newMarkerRows, Finset.mem_insert, Finset.mem_singleton] at hy ⊢
    tauto
  · exact cover_work l p (Finset.mem_sdiff.mp (row_touches p .west _ (Or.inl rfl) ht)).1

end PushPuzzle.Push.AcceptanceSoundness

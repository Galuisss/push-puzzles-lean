/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramStock
public import PushS.PortAxisFixed
import all PushS.PortAxisFixed
import all PushS.PortStreetEnumeration
import all PushS.PortSegments
import all Push.AcceptanceProgramLayout

/-! Actual auxiliary-column membership and level ownership of the emitted acceptance metadata. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS PushFS.Reduction Push.AcceptanceProgram

/-- The emitter's original ordinary and five-column gate auxiliary coordinate list. -/
def acceptanceAuxiliaryCoordinates (l : PortLayout) (p : Scales.Parameters) : List ℕ :=
  originalAuxiliary l (coordinates p)

/-- Original auxiliary stock belongs to the exact acceptance auxiliary set. -/
theorem acceptanceOriginalAux_mem (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) {x : ℕ}
    (hx : x ∈ l.acceptanceAuxiliaryCoordinates p) : x ∈ auxiliaries l p := by
  have hraw : x ∈ originalAuxiliary l (coordinates p) := hx
  have hbounds : 0 < x ∧ x < p.W := by
    rcases List.mem_append.mp hraw with he | hi
    · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp he
      apply column_inside p ((l.endpoints_port_lt hl he).trans_le ha)
      apply endpoint_columns_span p e
      simp only [List.mem_cons, List.not_mem_nil, or_false, endpointColumns] at hxe ⊢
      tauto
    · obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hi
      apply column_inside p (center_port l p hl ha hi)
      exact center_columns_span p i (List.mem_cons_of_mem _ hxi)
  apply Finset.mem_sdiff.mpr
  constructor
  · apply List.mem_toFinset.mpr
    exact List.mem_append_right _ hraw
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, hi⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact original_aux_off_axis l p hl hM i hraw hi.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega

private theorem acceptance_column_data (l : PortLayout) (p : Scales.Parameters) (side : Side)
    {a : Push.AcceptanceProgram.PageColumn} (ha : a ∈ Push.AcceptanceProgram.pageColumns l p side) :
    (∃ e ∈ l.endpoints, e.side = side ∧ a.level = e.level ∧
      a.column ∈ [(auxiliary (coordinates p) e).1, (auxiliary (coordinates p) e).2]) ∨
    (side = .lower ∧ a.level = 1 ∧ ∃ i ∈ centers l, a.column ∈ specialColumns (coordinates p) i) := by
  unfold Push.AcceptanceProgram.pageColumns at ha
  rcases List.mem_append.mp ha with ha | ha
  · obtain ⟨e, he, ha⟩ := List.mem_flatMap.mp ha
    obtain ⟨he, hside⟩ := List.mem_filter.mp he
    have hside : e.side = side := by simpa using hside
    left
    refine ⟨e, he, hside, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> simp only [List.mem_cons, List.not_mem_nil, or_false]
    · exact ⟨trivial, Or.inl rfl⟩
    · exact ⟨trivial, Or.inr rfl⟩
  · split at ha
    next hside =>
      obtain ⟨i, hi, ha⟩ := List.mem_flatMap.mp ha
      right
      refine ⟨hside, ?_, i, hi, ?_⟩
      all_goals
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;>
          simp only [specialColumns, coordinates, Coordinates.x, Scales.Parameters.x,
            List.mem_cons, List.not_mem_nil, or_false]
      all_goals tauto
    next hside => cases ha

/-- Every emitted acceptance-page column is an actual non-frame, non-axis auxiliary street. -/
theorem acceptancePageColumn_aux (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side)
    {a : Push.AcceptanceProgram.PageColumn} (hcol : a ∈ Push.AcceptanceProgram.pageColumns l p side) :
    a.column ∈ auxiliaries l p := by
  have hraw : a.column ∈ originalAuxiliary l (coordinates p) := by
    rcases acceptance_column_data l p side hcol with ⟨e, he, _, _, hx⟩ | ⟨_, _, i, hi, hx⟩
    · exact List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩)
    · exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨i, hi, hx⟩)
  have hbounds : 0 < a.column ∧ a.column < p.W := by
    rcases acceptance_column_data l p side hcol with ⟨e, he, _, _, hx⟩ | ⟨_, _, i, hi, hx⟩
    · apply column_inside p ((l.endpoints_port_lt hl he).trans_le ha)
      apply endpoint_columns_span p e
      simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hx ⊢
      tauto
    · apply column_inside p (center_port l p hl ha hi)
      exact center_columns_span p i (List.mem_cons_of_mem _ hx)
  apply Finset.mem_sdiff.mpr
  constructor
  · apply List.mem_toFinset.mpr
    exact List.mem_append_right _ hraw
  · intro hx
    rcases Finset.mem_union.mp hx with hx | hx
    · obtain ⟨i, _, hi⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
      exact original_aux_off_axis l p hl hM i hraw hi.symm
    · simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      omega

/-- Two upper-page metadata entries on one actual column have the same physical level. -/
theorem acceptanceUpperColumn_level (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {a b : Push.AcceptanceProgram.PageColumn}
    (ha : a ∈ Push.AcceptanceProgram.pageColumns l p .upper)
    (hb : b ∈ Push.AcceptanceProgram.pageColumns l p .upper) (hx : a.column = b.column) :
    a.level = b.level := by
  rcases acceptance_column_data l p .upper ha with ⟨e, he, hside, hla, hxa⟩ | ⟨hs, _⟩
  · rcases acceptance_column_data l p .upper hb with ⟨f, hf, hside', hlb, hxb⟩ | ⟨hs, _⟩
    · have hport : e.port = f.port := by
        apply column_owner p (x := a.column)
        · apply endpoint_columns_span p e
          simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hxa ⊢
          tauto
        · apply endpoint_columns_span p f
          rw [hx]
          simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hxb ⊢
          tauto
      have hef := l.endpoints_key_injective hl he hf (hside.trans hside'.symm) hport
      rw [hla, hlb, hef]
    · cases hs
  · cases hs

/-- Every actual gate center is one of the numbered principal axes. -/
theorem acceptanceCore_subset_axes (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    cores l p ⊆ axes l p := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hi
  apply List.mem_toFinset.mpr
  exact List.mem_map.mpr ⟨first + 1, List.mem_range.mpr (gate_middle_lt l hl hg), rfl⟩

/-- An actual auxiliary street is disjoint from the gate-center axes. -/
theorem acceptanceAux_not_core (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    {x : ℕ} (hx : x ∈ auxiliaries l p) : x ∉ cores l p := by
  intro hc
  exact (Finset.mem_sdiff.mp hx).2 (Finset.mem_union_left _ (l.acceptanceCore_subset_axes p hl hc))

end PushPuzzle.PushS.PortLayout

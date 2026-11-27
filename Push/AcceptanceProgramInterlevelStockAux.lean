/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortStreetSeparation
import all PushS.EndpointWalking
import all PushS.PortWalkBudget
import all PushS.PortLayoutCoordinates

/-! Every actual auxiliary street has literal page-column metadata. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS Push.AcceptanceProgram

private theorem auxiliary_raw (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ auxiliaries l p) : x ∈ originalAuxiliary l (coordinates p) := by
  obtain ⟨hs, hn⟩ := Finset.mem_sdiff.mp hx
  change x ∈ (streetColumns l (coordinates p)).toFinset at hs
  have hs := List.mem_toFinset.mp hs
  simp only [streetColumns, List.mem_append] at hs
  rcases hs with (hf | ha) | hs
  · have hf : x ∈ [0, p.W] := hf
    exact False.elim (hn (Finset.mem_union_right _ (by simpa only [List.mem_cons,
      List.not_mem_nil, or_false, Finset.mem_insert, Finset.mem_singleton] using hf)))
  · exact False.elim (hn (Finset.mem_union_left _ (List.mem_toFinset.mpr ha)))
  · exact hs

/-- Every non-frame, non-axis auxiliary street is emitted in some actual page-column metadata entry. -/
theorem acceptanceAux_pageColumn (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ auxiliaries l p) :
    ∃ side a, a ∈ Push.AcceptanceProgram.pageColumns l p side ∧ a.column = x := by
  rcases List.mem_append.mp (auxiliary_raw l p hx) with he | hg
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp he
    change x ∈ [(auxiliary (coordinates p) e).1, (auxiliary (coordinates p) e).2] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx
    · obtain ⟨a, ha, hc, _, _⟩ := endpoint_trim_column l p e he .f
      exact ⟨e.side, a, ha, hc.trans hx.symm⟩
    · obtain ⟨a, ha, hc, _, _⟩ := endpoint_trim_column l p e he .r
      exact ⟨e.side, a, ha, hc.trans hx.symm⟩
  · obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp hg
    have hi : i ∈ l.gateCenterCoordinates := hi
    change x ∈ [p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12] at hx
    have hcolumns : ∀ a ∈ ([⟨p.x i - 2, 1, false⟩, ⟨p.x i + 4, 1, true⟩,
        ⟨p.x i + 6, 1, false⟩, ⟨p.x i + 8, 1, false⟩, ⟨p.x i + 12, 1, false⟩] : List PageColumn),
        a ∈ Push.AcceptanceProgram.pageColumns l p .lower := by
      intro a ha
      unfold Push.AcceptanceProgram.pageColumns
      apply List.mem_append_right
      rw [ite_eq_left rfl]
      exact List.mem_flatMap.mpr ⟨i, hi, ha⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with hx | hx | hx | hx | hx
    · exact ⟨.lower, ⟨_, 1, false⟩, hcolumns _ (by simp), hx.symm⟩
    · exact ⟨.lower, ⟨_, 1, true⟩, hcolumns _ (by simp), hx.symm⟩
    · exact ⟨.lower, ⟨_, 1, false⟩, hcolumns _ (by simp), hx.symm⟩
    · exact ⟨.lower, ⟨_, 1, false⟩, hcolumns _ (by simp), hx.symm⟩
    · exact ⟨.lower, ⟨_, 1, false⟩, hcolumns _ (by simp), hx.symm⟩

end PushPuzzle.PushS.PortLayout

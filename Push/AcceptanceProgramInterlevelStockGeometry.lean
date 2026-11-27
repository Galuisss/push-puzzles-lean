/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockMarkers
public import Push.AcceptanceProgramLowerFinishStockColumns
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all PushS.PortSegments
import all PushS.PortStreetSeparation
import all PushS.PortStreetEnumeration
import all PushS.PortCoreCrossing
import all PushS.PortWalkBudget

/-! The marker columns avoid the actual guard and lower sample probes. -/

public section
namespace PushPuzzle.PushS.PortLayout

open PushFS Push.AcceptanceProgram

/-- Every literal page-column entry retains its actual positive allocated level. -/
theorem acceptancePageColumn_level_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (side : Side) {a : PageColumn}
    (ha : a ∈ Push.AcceptanceProgram.pageColumns l p side) : 1 ≤ a.level ∧ a.level ≤ p.levels := by
  rcases acceptance_column_data l p side ha with ⟨e, he, _, hlevel, _⟩ | ⟨_, hlevel, _⟩
  · rw [hlevel]
    exact l.endpoints_level_bounds p hl hM he
  · rw [hlevel]
    exact ⟨le_rfl, p.levels_pos⟩

/-- A shared page-column coordinate has one literal level in that page's metadata. -/
theorem acceptancePageColumn_level_eq (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {a b : PageColumn}
    (ha : a ∈ Push.AcceptanceProgram.pageColumns l p side)
    (hb : b ∈ Push.AcceptanceProgram.pageColumns l p side) (hx : a.column = b.column) : a.level = b.level := by
  cases side
  · exact l.acceptanceUpperColumn_level p hl ha hb hx
  · exact l.acceptanceLowerColumn_level p hl ha hb hx

/-- The actual guard filter excludes every original street column. -/
theorem acceptanceStreet_not_guard (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hs : x ∈ l.streetColumnCoordinates p) : x ∉ guards l p := by
  intro hg
  have hg : x ∈ guardColumns l (coordinates p) (l.fixedSegments p) := List.mem_toFinset.mp hg
  obtain ⟨s, _, he⟩ := List.mem_filterMap.mp hg
  split at he
  next hp =>
    have he := Option.some.inj he
    have hn := hp.2.1
    simp only [he, Bool.not_eq_true', Bool.eq_false_iff] at hn
    exact hn (List.contains_iff_mem.mpr hs)
  next hp => cases he

/-- The actual guard filter excludes every original auxiliary street. -/
theorem acceptanceAux_not_guard (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ auxiliaries l p) : x ∉ guards l p :=
  l.acceptanceStreet_not_guard p (List.mem_toFinset.mp (Finset.mem_sdiff.mp hx).1)

/-- An actual lower-page auxiliary metadata column never coincides with either short-train sample. -/
theorem acceptanceLowerColumn_not_sample (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) {a : PageColumn}
    (ha : a ∈ Push.AcceptanceProgram.pageColumns l p .lower) : a.column ∉ samples l p := by
  intro hs
  obtain ⟨i, hi, hx⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hs)
  have hi : i ∈ centers l := hi
  have hspan : p.x i - columnRadius p ≤ a.column ∧ a.column ≤ p.x i + columnRadius p := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    dsimp only [columnRadius]
    omega
  rcases acceptance_column_data l p .lower ha with ⟨e, he, hside, _, hcol⟩ | ⟨_, _, k, hk, hcol⟩
  · have hport : e.port = i := by
      apply column_owner p (x := a.column) _ hspan
      apply endpoint_columns_span p e
      simp only [endpointColumns, List.mem_cons, List.not_mem_nil, or_false] at hcol ⊢
      tauto
    obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
    exact l.endpoints_lower_ne_gate_middle hl hg he hside (hport.trans hm)
  · have hport : k = i := by
      apply column_owner p (x := a.column) _ hspan
      apply center_columns_span p k
      exact List.mem_cons_of_mem _ hcol
    subst k
    change a.column ∈ [p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12] at hcol
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcol hx
    omega

end PushPuzzle.PushS.PortLayout

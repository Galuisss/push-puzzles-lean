/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/
module

public import Push.AcceptanceProgramInterlevelStockWork
public import PushS.PortGateHalfMarkers
import all Push.AcceptanceProgramInterlevelStock
import all Push.AcceptanceProgramInterlevelStockReads
import all Push.AcceptanceProgramInterlevelStockWork
import all Push.AcceptanceProgramColumns
import all Push.AcceptanceProgramLayout
import all PushS.PortGateHalfMarkers
import all PushS.PortSegments
import all PushS.PortStreetEnumeration

/-! The literal half-depth markers avoid the actual earlier public and axis prefixes. -/

public section
namespace PushPuzzle.Push.AcceptanceProgram

open PushFS PushS PushS.PortLayout

/-- Every private acceptance column is a genuine gate's +4 column. -/
theorem privateColumn_gate (l : PortLayout) (p : Scales.Parameters) {x : ℕ}
    (hx : x ∈ privateColumns l p) : ∃ i ∈ l.gateCenterCoordinates, x = p.x i + 4 := by
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hx)
  obtain ⟨ha, hp⟩ := List.mem_filter.mp ha
  unfold pageColumns at ha
  rcases List.mem_append.mp ha with he | hg
  · obtain ⟨_, _, ha⟩ := List.mem_flatMap.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> cases hp
  · rw [ite_eq_left rfl] at hg
    obtain ⟨i, hi, ha⟩ := List.mem_flatMap.mp hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> first
      | exact ⟨i, hi, rfl⟩
      | cases hp

/-- Every selected half-depth coordinate is one of the emitter's literal fixed holes. -/
theorem half_target (l : PortLayout) (p : Scales.Parameters) (target : List Bool)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2)
    (hx : q.1.val ∈ cores l p ∪ privateColumns l p) : q ∈ targetHoles l p target := by
  apply l.gateHalfMarkers_subset_encoded p (l.canonical target)
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _, ?_⟩
  have hd := readDepth_eq p le_rfl p.levels_pos
  rcases Finset.mem_union.mp hx with hc | hp
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact ⟨i, hi, Or.inl he.symm, by simpa only [hd] using hy⟩
  · obtain ⟨i, hi, he⟩ := privateColumn_gate l p hp
    exact ⟨i, hi, Or.inr he, by simpa only [hd] using hy⟩

private theorem half_data (l : PortLayout) (p : Scales.Parameters)
    {q : Cell (p.W + 1) (p.H + 1)} (hx : q.1.val ∈ cores l p ∪ privateColumns l p) :
    ∃ i ∈ l.gateCenterCoordinates, q.1.val = p.x i ∨ q.1.val = p.x i + 4 := by
  rcases Finset.mem_union.mp hx with hc | hp
  · obtain ⟨i, hi, he⟩ := List.mem_map.mp (List.mem_toFinset.mp hc)
    exact ⟨i, hi, Or.inl he.symm⟩
  · obtain ⟨i, hi, he⟩ := privateColumn_gate l p hp
    exact ⟨i, hi, Or.inr he⟩

private theorem half_not_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2)
    (hx : q.1.val ∈ cores l p ∪ privateColumns l p) : q ∉ Boundary.frame := by
  obtain ⟨i, hi, hx⟩ := half_data l p hx
  have hy' : q.2.val = p.H - readDepth p 1 / 2 := by
    simpa only [readDepth_eq p le_rfl p.levels_pos] using hy
  exact gate_window_not_frame l p hl ha hi (half_marker_window p hx hy')

private theorem half_not_trim (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2)
    (hx : q.1.val ∈ cores l p ∪ privateColumns l p) : q ∉ (trimRound l p side).region := by
  obtain ⟨i, hi, hxi⟩ := half_data l p hx
  have hspan := center_columns_span p i (show q.1.val ∈ centerColumns p i from by
    change q.1.val ∈ [p.x i, p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12]
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    tauto)
  intro ht
  obtain ⟨a, ha, hp, hxa, hd⟩ := (mem_trim_region l p side q).mp ht
  cases side with
  | upper =>
    have hb := l.acceptancePageColumn_level_bounds p hl hM .upper ha
    have htD := trimDepth_lt_D p hb.1
    have hY := readDepth_add_lt_D p 1
    rw [readDepth_eq p le_rfl p.levels_pos] at hY
    have hh : p.H = 2 * p.D := rfl
    simp only [pageDepth, ite_true] at hd
    omega
  | lower =>
    unfold pageColumns at ha
    rcases List.mem_append.mp ha with he | hg
    · obtain ⟨e, hefilter, ha⟩ := List.mem_flatMap.mp he
      obtain ⟨hendpoint, hs⟩ := List.mem_filter.mp hefilter
      have hs : e.side = .lower := by simpa using hs
      have hep : e.port = i := by
        apply column_owner p (x := q.1.val) _ hspan
        apply endpoint_columns_span p e
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl <;> simp [endpointColumns, hxa, EndpointStreet.column]
      obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
      exact l.endpoints_lower_ne_gate_middle hl hg hendpoint hs (hep.trans hm)
    · rw [ite_eq_left rfl] at hg
      obtain ⟨j, hj, ha⟩ := List.mem_flatMap.mp hg
      have hja : a.column ∈ centerColumns p j := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl | rfl <;> simp [centerColumns, specialColumns, coordinates, Coordinates.x, Scales.Parameters.x]
      have heij : j = i := column_owner p (hxa ▸ center_columns_span p j hja) hspan
      subst j
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl
      all_goals simp only [Bool.true_eq_false] at hp
      all_goals have hlo := readLength_add_lt_x p i 0
      all_goals rcases hxi with hxi | hxi <;> dsimp at hxa <;> omega

private theorem half_not_main (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (side : Side)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - p.Y 1 / 2)
    (hx : q.1.val ∈ cores l p ∪ privateColumns l p) : q ∉ (mainRound l p side).region := by
  obtain ⟨i, hi, hxi⟩ := half_data l p hx
  intro ht
  obtain ⟨_, hr, hcol, hdepth⟩ := (mem_readRegion _ _ q).mp ht
  obtain ⟨e, hefilter, rfl⟩ := List.mem_map.mp hr
  obtain ⟨hendpoint, hs⟩ := List.mem_filter.mp hefilter
  have hs : e.side = side := by simpa using hs
  obtain ⟨hj, hjm⟩ := l.endpoints_level_bounds p hl hM hendpoint
  have hY := readDepth_add_lt_D p e.level
  rw [readDepth_eq p hj hjm] at hY
  have hY1 := readDepth_add_lt_D p 1
  rw [readDepth_eq p le_rfl p.levels_pos] at hY1
  have hh : p.H = 2 * p.D := rfl
  cases side with
  | upper =>
    simp only [ite_true, prefixRank] at hdepth
    omega
  | lower =>
    change q.1.val = p.x e.port at hcol
    have hep : e.port = i := by
      apply column_owner p (x := q.1.val)
      · apply endpoint_columns_span p e
        rw [hcol]
        simp [endpointColumns, coordinates, Coordinates.x, Scales.Parameters.x]
      · apply center_columns_span p i
        change q.1.val ∈ [p.x i, p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12]
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        tauto
    obtain ⟨kind, first, hg, hm⟩ := center_gate_mem l hi
    exact l.endpoints_lower_ne_gate_middle hl hg hendpoint hs (hep.trans hm)

end PushPuzzle.Push.AcceptanceProgram

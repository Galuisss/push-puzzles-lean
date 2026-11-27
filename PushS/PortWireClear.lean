/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortWireGeometry
import all PushS.PortWireGeometry
import all PushS.PortWireIndexing
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-! The complete marked fixed background avoids each ordinary WIRE's pushing interval. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem working_row_gap (p : Scales.Parameters) (side : Side) (j : ℕ) :
    onSide (coordinates p) side (readDepth p j) + 32 < p.D ∨
      p.D + 32 < onSide (coordinates p) side (readDepth p j) := by
  have hy := readDepth_add_lt_D p j
  have hH : p.H = 2 * p.D := rfl
  cases side <;> simp only [onSide, coordinates, ite_true, reduceCtorEq, ite_false] <;> omega

private theorem interior_wire_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {g : Placement}
    (hg : g ∈ placements l) (hw : g.gate = none) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (interiorFixed l (coordinates p)))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left < q.1) (hhi : q.1 < p.x g.right) : False := by
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  simp only [interiorFixed, List.mem_append, or_assoc] at hmem
  rcases hmem with hmem | hmem | hmem | hmem | hmem
  · obtain ⟨e, he, hmem⟩ := List.mem_flatMap.mp hmem
    exact wire_fixed_endpoint_clear l p hl hM hg hw he ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩)
      hy hlo hhi
  · obtain ⟨i, _, hmem⟩ := List.mem_flatMap.mp hmem
    exact wire_fixed_gate_clear l p hl hM hg hw i ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩) hy
  · exact wire_wide_clear l p hl hg hw .upper ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩) hy hlo hhi
  · exact wire_wide_clear l p hl hg hw .lower ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩) hy hlo hhi
  · obtain ⟨x, _, rfl⟩ := List.mem_map.mp hmem
    have hp := point_coordinates hq
    simp only [coordinates] at hp
    have hgap := working_row_gap p g.side g.level
    omega

private theorem shifted_wire_clear (p : Scales.Parameters) (g : Placement)
    (ss : List Segment) (guards rows : List ℕ)
    (hss : ∀ q ∈ pointHoles ss,
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left < q.1 → q.1 < p.x g.right → False) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (ss.map (shiftPoint guards rows)))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False := by
  obtain ⟨image, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hmem
  unfold shiftPoint at hq
  split at hq
  · rename_i hc
    have hp := point_coordinates hq
    have hm := Nat.mod_lt s.start.1 (by decide : 0 < 2)
    have hstart : s.Contains s.start := by simp [Segment.Contains, hc.1]
    exact hss s.start ((mem_pointHoles _ _).mpr ⟨s, hs, hstart⟩) (by omega) (by omega) (by omega)
  · exact hss q ((mem_pointHoles _ q).mpr ⟨s, hs, hq⟩) hy (by omega) (by omega)

private theorem marked_workrow_clear (l : PortLayout) (p : Scales.Parameters)
    (g : Placement)
    (hinside : ∀ q ∈ pointHoles (interiorFixed l (coordinates p)),
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left < q.1 → q.1 < p.x g.right → False) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (markedInterior l (coordinates p)))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False := by
  unfold markedInterior at hq
  extract_lets base guards shifted aux marked at hq
  have hbase : ∀ q ∈ pointHoles base,
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left < q.1 → q.1 < p.x g.right → False :=
    hinside
  have hshift : ∀ q ∈ pointHoles shifted,
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left + 2 ≤ q.1 → q.1 ≤ p.x g.right - 2 → False := by
    dsimp only [shifted]
    split
    · exact fun _ h hy hlo hhi => shifted_wire_clear p g base guards _ hbase h hy hlo hhi
    · exact fun q h hy hlo hhi => hbase q h hy (by omega) (by omega)
  have hmarked : ∀ q ∈ pointHoles marked,
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left + 2 ≤ q.1 → q.1 ≤ p.x g.right - 2 → False := by
    intro q hq hy hlo hhi
    rw [pointHoles_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact hshift q hq hy hlo hhi
    · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
      obtain ⟨x, _, hs⟩ := List.mem_flatMap.mp hs
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals have hp := point_coordinates hq
      all_goals have hgap := working_row_gap p g.side g.level
      all_goals simp only [coordinates] at hp
      all_goals omega
  change q ∈ pointHoles ((marked ++ _) ++ _) at hq
  rw [pointHoles_append, pointHoles_append, Finset.mem_union, Finset.mem_union] at hq
  rcases hq with (hq | hq) | hq
  · exact hmarked q hq hy hlo hhi
  · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨x, _, rfl⟩ := List.mem_map.mp hs
    have hp := point_coordinates hq
    simp only [coordinates] at hp
    have hgap := working_row_gap p g.side g.level
    omega
  · obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have hp := point_coordinates hq
    all_goals simp only [coordinates] at hp
    all_goals have hgap := working_row_gap p g.side g.level
    all_goals omega

private theorem fixed_workrow_clear (l : PortLayout) (p : Scales.Parameters)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    (g : Placement) (hports : g.left < g.right ∧ g.right < l.portCount)
    (hlevel : 1 ≤ g.level ∧ g.level ≤ l.pages.highest)
    (hinside : ∀ q ∈ pointHoles (interiorFixed l (coordinates p)),
      q.2 = onSide (coordinates p) g.side (readDepth p g.level) →
        p.x g.left < q.1 → q.1 < p.x g.right → False) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.fixedSegments p))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False := by
  rw [fixedSegments, pointHoles_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hb := hports
    have hx := readLength_add_lt_x p g.left 0
    have hxr := x_add_readLength_lt_W p (lt_of_lt_of_le hb.2 ha) 0
    have hj := hlevel
    have hY := readDepth_ge p hj.1 (show g.level ≤ p.levels by omega)
    have hH := readDepth_add_lt_H p g.level
    have hrow : 0 < q.2 ∧ q.2 < p.H := by
      cases hs : g.side <;> simp [hs, onSide, coordinates] at hy <;> omega
    obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
    simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · have hp := horizontal_coordinates hq; omega
    · have hp := horizontal_coordinates hq
      change q.2 = p.H ∧ _ at hp
      omega
    · have hp := vertical_coordinates hq; omega
    · have hp := vertical_coordinates hq
      change q.1 = p.W ∧ _ at hp
      omega
  · exact marked_workrow_clear l p g hinside hq hy hlo hhi

private theorem wire_fixed_clear (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {g : Placement} (hg : g ∈ placements l) (hw : g.gate = none) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.fixedSegments p))
    (hy : q.2 = onSide (coordinates p) g.side (readDepth p g.level))
    (hlo : p.x g.left + 2 ≤ q.1) (hhi : q.1 ≤ p.x g.right - 2) : False :=
  fixed_workrow_clear l p hM ha g (wire_ports l hl hg hw) (placement_level_bounds l hl hg)
    (fun _ h hy hlo hhi => interior_wire_clear l p hl hM hg hw h hy hlo hhi) hq hy hlo hhi

end PushPuzzle.PushS.PortLayout

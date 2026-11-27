/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePageWindow
import all PushS.PortGatePageWindow
import all PushS.PortAxisClear
import all PushS.PortCoreCrossing
import all PushS.PortStreetSeparation
import all PushS.PortWalkBudget
import all PushS.PortSegments

/-! On a principal axis the actual fixed-hole recipe consists of frame and gate half-depth holes. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem special_off_axis (p : Scales.Parameters) (i k : ℕ) {x : ℕ}
    (hx : x ∈ specialColumns (coordinates p) i) : x ≠ p.x k := by
  have hx0 := readLength_add_lt_x p i 0
  have hspan : p.x i - 12 ≤ x ∧ x ≤ p.x i + 12 := by
    change x ∈ [p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  by_cases hik : i = k
  · subst k
    change x ∈ [p.x i - 2, p.x i + 4, p.x i + 6, p.x i + 8, p.x i + 12] at hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega
  · exact off_axis_of_span p hik (by have := readDepth_readLength_margin p 0 0; omega) hspan

private theorem original_aux_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (k : ℕ) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) : x ≠ p.x k := by
  rcases List.mem_append.mp hx with he | hi
  · obtain ⟨e, he, hx⟩ := List.mem_flatMap.mp he
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    exact auxiliary_off_axis l p hl hM he k hx
  · obtain ⟨i, _, hx⟩ := List.mem_flatMap.mp hi
    exact special_off_axis p i k hx

private theorem gate_fixed_axis (l : PortLayout) (p : Scales.Parameters) {i k : ℕ}
    (hi : i ∈ centers l) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateFixedSegments (coordinates p) i)) (hx : q.1 = p.x k) :
    k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
  have hspan := gate_fixed_span p i hq
  have hik : i = k := by
    by_contra hn
    exact off_axis_of_span p hn (r := 12) (by have := readDepth_readLength_margin p 0 0; omega) (by omega) hx
  subst i
  refine ⟨hi, ?_⟩
  have hx0 := readLength_add_lt_x p k 0
  cases gateFixedSegments_location p k hq with
  | publicStreet hc _ =>
    simp only [gatePublicColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
    omega
  | privateCap hc _ => omega
  | privateBranch _ hs => omega
  | halfDepth hy => exact hy
  | marker _ hc _ => exact False.elim (special_off_axis p k k hc hx)

private theorem interior_axis_source (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {k : ℕ} (hk : k < l.portCount)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (interiorFixed l (coordinates p))) (hx : q.1 = p.x k) :
    k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
  simp only [interiorFixed, List.mem_append, or_assoc] at hs
  rcases hs with hs | hs | hs | hs | hs
  · obtain ⟨e, he, hs⟩ := List.mem_flatMap.mp hs
    exact False.elim (endpoint_fixed_off_axis l p hl hM he k ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hx)
  · obtain ⟨i, hi, hs⟩ := List.mem_flatMap.mp hs
    exact gate_fixed_axis l p hi ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hx
  · exact False.elim (wide_fixed_off_axis l p hl .upper hk ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hx)
  · exact False.elim (wide_fixed_off_axis l p hl .lower hk ((mem_pointHoles _ _).mpr ⟨s, hs, hc⟩) hx)
  · obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hs
    exact False.elim (original_aux_off_axis l p hl hM k hx' ((point_coordinates hc).1.symm.trans hx))

private theorem shifted_axis_source (l : PortLayout) (p : Scales.Parameters) {k : ℕ}
    (hk : k < l.portCount) (ss source : List Segment) (rows : List ℕ)
    (hss : ∀ q ∈ pointHoles ss, q.1 = p.x k → k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (ss.map (shiftPoint (guardColumns l (coordinates p) source) rows)))
    (hx : q.1 = p.x k) : k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
  obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨s, hs0, rfl⟩ := List.mem_map.mp hs
  unfold shiftPoint at hc
  split at hc
  · rename_i hshift
    have hguard := guard_axis_far l p source (List.contains_iff_mem.mp hshift.2.1) hk
    have hp := point_coordinates hc
    have hmod := Nat.mod_lt s.start.1 (by decide : 0 < 2)
    simp only [Nat.dist_eq_max_sub_min] at hguard
    omega
  · exact hss q ((mem_pointHoles _ q).mpr ⟨s, hs0, hc⟩) hx

private theorem marked_axis_source (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {k : ℕ} (hk : k < l.portCount)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (markedInterior l (coordinates p))) (hx : q.1 = p.x k) :
    k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
  unfold markedInterior at hq
  extract_lets base guards shifted aux marked at hq
  have hbase : ∀ q ∈ pointHoles base, q.1 = p.x k → k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 :=
    fun _ h hcol => interior_axis_source l p hl hM hk h hcol
  have hshift : ∀ q ∈ pointHoles shifted, q.1 = p.x k → k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
    dsimp only [shifted]
    split
    · exact fun _ h hcol => shifted_axis_source l p hk base _ _ hbase h hcol
    · exact hbase
  have hmarked : ∀ q ∈ pointHoles marked, q.1 = p.x k → k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2 := by
    intro q hq hx
    rw [pointHoles_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact hshift q hq hx
    · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
      obtain ⟨x, hx', hs⟩ := List.mem_flatMap.mp hs
      have haxis : (axisColumns l (coordinates p)).contains (p.x k) = true :=
        List.contains_iff_mem.mpr (List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      all_goals have heq : x = p.x k := (point_coordinates hc).1.symm.trans hx
      all_goals subst x
      all_goals have hf := (List.mem_filter.mp hx').2
      all_goals simp only [haxis, Bool.not_true, Bool.and_false, Bool.false_eq_true] at hf
  change q ∈ pointHoles ((marked ++ _) ++ _) at hq
  rw [pointHoles_append, pointHoles_append, Finset.mem_union, Finset.mem_union] at hq
  rcases hq with (hq | hq) | hq
  · exact hmarked q hq hx
  · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨x, hx', rfl⟩ := List.mem_map.mp hs
    have hfar := guard_axis_far l p _ hx' hk
    have hp := point_coordinates hc
    rw [hp.1.symm, hx] at hfar
    simp at hfar
  · obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨i, _, hs⟩ := List.mem_flatMap.mp hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl
    all_goals have hp := (point_coordinates hc).1
    all_goals change q.1 = p.x i + _ at hp
    all_goals by_cases hik : i = k
    all_goals first
      | subst i; omega
      | exact False.elim (off_axis_of_span p hik (r := 12)
          (by have := readDepth_readLength_margin p 0 0; omega) (by omega) hx)

/-- The complete fixed recipe meets a principal axis only at the frame or its gate half-depth marker. -/
theorem fixedSegments_on_main_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {k : ℕ} (hk : k < l.portCount) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.fixedSegments p)) (hx : q.1 = p.x k) :
    q.2 = 0 ∨ q.2 = p.H ∨ (k ∈ l.gateCenterCoordinates ∧ q.2 = p.H - readDepth p 1 / 2) := by
  rw [fixedSegments, pointHoles_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hx0 := readLength_add_lt_x p k 0
    have hxW := x_add_readLength_lt_W p (hk.trans_le ha) 0
    obtain ⟨s, hs, hc⟩ := (mem_pointHoles _ q).mp hq
    simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · exact Or.inl (horizontal_coordinates hc).1
    · exact Or.inr (Or.inl (horizontal_coordinates hc).1)
    · have hp := (vertical_coordinates hc).1
      change q.1 = 0 at hp
      omega
    · have hp := (vertical_coordinates hc).1
      change q.1 = p.W at hp
      omega
  · exact Or.inr (Or.inr (marked_axis_source l p hl hM hk hq hx))

end PushPuzzle.PushS.PortLayout

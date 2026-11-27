/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortFixedSeparation
import all PushS.PortFixedSeparation
import all PushS.PortSignalLocality
import all PushS.PortCoreCrossing
import all PushS.PortEndpointCrossing
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-! The actual fixed background leaves every ordinary shared axis clear inside the frame. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

private theorem off_axis_of_span (p : Scales.Parameters) {i k r x : ℕ}
    (hik : i ≠ k) (hr : r + 2 < p.D)
    (hx : p.x i - r ≤ x ∧ x ≤ p.x i + r) : x ≠ p.x k := by
  rcases lt_or_gt_of_ne hik with h | h
  · have := axis_spacing p h; omega
  · have := axis_spacing p h; omega

private theorem auxiliary_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) (k : ℕ) {x : ℕ}
    (hx : x = (auxiliary (coordinates p) e).1 ∨ x = (auxiliary (coordinates p) e).2) :
    x ≠ p.x k := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hL : 16384 ≤ (coordinates p).length e.level := readLength_ge p hj hm
  have hmarg : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  by_cases hk : e.port = k
  · rw [← hk]
    change x ≠ (coordinates p).x e.port
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hx <;> omega
  · apply off_axis_of_span p hk (r := readLength p e.level + 2)
      (by have := readDepth_readLength_margin p 0 e.level; omega)
    change (coordinates p).x e.port - ((coordinates p).length e.level + 2) ≤ x ∧
      x ≤ (coordinates p).x e.port + (coordinates p).length e.level + 2
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hx <;> omega

private theorem own_fixed_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : q.1 ≠ p.x e.port := by
  obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM he
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  have hL : 16384 ≤ (coordinates p).length e.level := readLength_ge p hj hm
  change q.1 ≠ (coordinates p).x e.port
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · exact auxiliary_off_axis l p hl hM he e.port (Or.inl (vertical_coordinates hq).1)
  · exact auxiliary_off_axis l p hl hM he e.port (Or.inr (vertical_coordinates hq).1)
  · have hh := horizontal_coordinates hq
    cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hh <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    all_goals split at hs
    all_goals simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    all_goals subst s
    all_goals have hp := point_coordinates hq
    all_goals cases hd : e.inward <;> simp [auxiliary, outward, inward, hd] at hp <;> omega
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl | rfl
      · exact auxiliary_off_axis l p hl hM he e.port (Or.inl (point_coordinates hq).1)
      · exact auxiliary_off_axis l p hl hM he e.port (Or.inr (point_coordinates hq).1)
    · cases hs

private theorem endpoint_fixed_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) (k : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e)) : q.1 ≠ p.x k := by
  by_cases hk : e.port = k
  · rw [← hk]
    exact own_fixed_off_axis l p hl hM he hq
  · exact off_axis_of_span p hk (by have := readDepth_readLength_margin p 0 e.level; omega)
      (fixed_endpoint_span l p e hq)

private theorem gate_middle_ne (l : PortLayout) (hl : l.pages.Valid) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .lower) {i : ℕ} (hi : i ∈ centers l) : i ≠ e.port := by
  obtain ⟨kind, first, hg, rfl⟩ := center_gate_mem l hi
  exact (l.endpoints_lower_ne_gate_middle hl hg he hs).symm

private theorem originalAuxiliary_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .lower) {x : ℕ}
    (hx : x ∈ originalAuxiliary l (coordinates p)) : x ≠ p.x e.port := by
  simp only [originalAuxiliary, List.mem_append, List.mem_flatMap] at hx
  rcases hx with ⟨f, hf, hx⟩ | ⟨i, hi, hx⟩
  · apply auxiliary_off_axis l p hl hM hf e.port
    simpa only [List.mem_cons, List.not_mem_nil, or_false] using hx
  · apply off_axis_of_span p (gate_middle_ne l hl he hs hi) (r := 12)
      (by have := readDepth_readLength_margin p 0 0; omega)
    have hm : 64 < (coordinates p).x i := by
      change 64 < p.x i
      have := readLength_add_lt_x p i 0; omega
    change (coordinates p).x i - 12 ≤ x ∧ x ≤ (coordinates p).x i + 12
    simp only [specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

private theorem wide_fixed_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (side : Side) {k : ℕ} (hk : k < l.portCount) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (wideFixed l (coordinates p) side)) : q.1 ≠ p.x k := by
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨⟨a, b⟩, hab, hs⟩ := List.mem_flatMap.mp hs
  dsimp only at hs
  split at hs
  · rename_i hgap
    obtain ⟨y, _, hs⟩ := List.mem_filterMap.mp hs
    split at hs
    · cases hs
    · simp only [Option.some.injEq] at hs
      subst s
      have hp := point_coordinates hq
      have hf := wide_midpoint_far l p hl side hab hgap hk
      rw [← hp.1] at hf
      intro h; simp [h] at hf
  · cases hs

private theorem interior_fixed_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .lower) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (interiorFixed l (coordinates p))) : q.1 ≠ p.x e.port := by
  obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
  dsimp only [interiorFixed] at hmem
  simp only [List.mem_append, or_assoc] at hmem
  rcases hmem with hmem | hmem | hmem | hmem | hmem
  · obtain ⟨f, hf, hmem⟩ := List.mem_flatMap.mp hmem
    exact endpoint_fixed_off_axis l p hl hM hf e.port ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩)
  · obtain ⟨i, hi, hmem⟩ := List.mem_flatMap.mp hmem
    have hspan := gate_fixed_span p i ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩)
    exact off_axis_of_span p (gate_middle_ne l hl he hs hi) (r := 12)
      (by have := readDepth_readLength_margin p 0 0; omega) (by omega)
  · exact wide_fixed_off_axis l p hl .upper (l.endpoints_port_lt hl he)
      ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩)
  · exact wide_fixed_off_axis l p hl .lower (l.endpoints_port_lt hl he)
      ((mem_pointHoles _ q).mpr ⟨s, hmem, hq⟩)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
    have hpos := point_coordinates hq
    rw [hpos.1]
    exact originalAuxiliary_off_axis l p hl hM he hs hx

private theorem shifted_off_axis (l : PortLayout) (p : Scales.Parameters) {i : ℕ}
    (hi : i < l.portCount) (ss source : List Segment) (rows : List ℕ)
    (hss : ∀ q ∈ pointHoles ss, q.1 ≠ p.x i) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (ss.map (shiftPoint (guardColumns l (coordinates p) source) rows))) :
    q.1 ≠ p.x i := by
  obtain ⟨image, himage, hq⟩ := (mem_pointHoles _ q).mp hq
  obtain ⟨s, hs0, rfl⟩ := List.mem_map.mp himage
  unfold shiftPoint at hq
  split at hq
  · rename_i hc
    have hg : s.start.1 ∈ guardColumns l (coordinates p) source := by
      simpa only [List.contains_iff_mem] using hc.2.1
    have hfar := guard_axis_far l p source hg hi
    have hp := point_coordinates hq
    have hmod := Nat.mod_lt s.start.1 (by decide : 0 < 2)
    simp only [Nat.dist_eq_max_sub_min] at hfar
    omega
  · exact hss q ((mem_pointHoles _ q).mpr ⟨s, hs0, hq⟩)

private theorem marked_fixed_off_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) {e : Endpoint}
    (he : e ∈ l.endpoints) (hs : e.side = .lower) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (markedInterior l (coordinates p))) : q.1 ≠ p.x e.port := by
  unfold markedInterior at hq
  extract_lets base guards shifted aux marked at hq
  have hi := l.endpoints_port_lt hl he
  have hbase : ∀ q ∈ pointHoles base, q.1 ≠ p.x e.port :=
    fun _ h => interior_fixed_off_axis l p hl hM he hs h
  have hshift : ∀ q ∈ pointHoles shifted, q.1 ≠ p.x e.port := by
    dsimp only [shifted]
    split
    · exact fun _ h => shifted_off_axis l p hi base (frame (coordinates p) ++ base) _ hbase h
    · exact hbase
  have hmarked : ∀ q ∈ pointHoles marked, q.1 ≠ p.x e.port := by
    intro q hq
    rw [pointHoles_append, Finset.mem_union] at hq
    rcases hq with hq | hq
    · exact hshift q hq
    · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
      obtain ⟨x, hx, hmem⟩ := List.mem_flatMap.mp hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with rfl | rfl
      all_goals
        have hp := point_coordinates hq
        intro hcol
        have heq : x = p.x e.port := hp.1.symm.trans hcol
        subst x
        have haxis : (axisColumns l (coordinates p)).contains (p.x e.port) = true :=
          List.contains_iff_mem.mpr (List.mem_map.mpr ⟨e.port, List.mem_range.mpr hi, rfl⟩)
        have hfilter := (List.mem_filter.mp hx).2
        simp only [haxis, Bool.not_true, Bool.and_false, Bool.false_eq_true] at hfilter
  change q ∈ pointHoles ((marked ++ _) ++ _) at hq
  rw [pointHoles_append, pointHoles_append, Finset.mem_union, Finset.mem_union] at hq
  rcases hq with (hq | hq) | hq
  · exact hmarked q hq
  · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hmem
    have hp := point_coordinates hq
    have hfar := guard_axis_far l p _ hx hi
    rw [← hp.1] at hfar
    intro h; simp [h] at hfar
  · obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
    obtain ⟨i, hi, hmem⟩ := List.mem_flatMap.mp hmem
    apply off_axis_of_span p (gate_middle_ne l hl he hs hi) (r := 12)
      (by have := readDepth_readLength_margin p 0 0; omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl
    all_goals have hp := point_coordinates hq
    all_goals change (coordinates p).x i - 12 ≤ q.1 ∧ q.1 ≤ (coordinates p).x i + 12
    all_goals omega

/-- The complete marked fixed background meets an ordinary shared axis only at its frame. -/
theorem fixedSegments_on_ordinary_axis (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {e : Endpoint} (he : e ∈ l.endpoints) (hs : e.side = .lower) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (l.fixedSegments p)) (hcol : q.1 = p.x e.port) :
    q.2 = 0 ∨ q.2 = p.H := by
  rw [fixedSegments, pointHoles_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have hx := readLength_add_lt_x p e.port 0
    have hxr := x_add_readLength_lt_W p (lt_of_lt_of_le (l.endpoints_port_lt hl he) ha) 0
    obtain ⟨s, hmem, hq⟩ := (mem_pointHoles _ q).mp hq
    simp only [frame, List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl | rfl
    · have h := horizontal_coordinates hq; exact Or.inl h.1
    · have h := horizontal_coordinates hq; exact Or.inr h.1
    · have h := vertical_coordinates hq
      change q.1 = 0 ∧ _ at h
      omega
    · have h := vertical_coordinates hq
      change q.1 = p.W ∧ _ at h
      omega
  · exact False.elim (marked_fixed_off_axis l p hl hM he hs hq hcol)

end PushPuzzle.PushS.PortLayout

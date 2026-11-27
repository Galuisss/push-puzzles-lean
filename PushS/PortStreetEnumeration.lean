/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortTwoPageStreets
import all PushS.PortTwoPageStreets
import all PushS.PortEndpointEnumeration
import all PushS.PortEndpointCrossing
import all PushS.PortCoreCrossing
import all PushS.PortSegmentBounds
import all PushS.PortSegments

/-! The actual per-page street columns are enumerated without repetition. -/

public section

namespace PushPuzzle.PushS.PortLayout


open PageLevels

private def endpointColumns (p : Scales.Parameters) (e : Endpoint) : List ℕ :=
  let (f, r) := auxiliary (coordinates p) e
  [f, (coordinates p).x e.port, r]

private def centerColumns (p : Scales.Parameters) (i : ℕ) : List ℕ :=
  (coordinates p).x i :: specialColumns (coordinates p) i

private def columnRadius (p : Scales.Parameters) : ℕ := p.L p.levels + 12

private theorem column_owner (p : Scales.Parameters) {i j x : ℕ}
    (hi : p.x i - columnRadius p ≤ x ∧ x ≤ p.x i + columnRadius p)
    (hj : p.x j - columnRadius p ≤ x ∧ x ≤ p.x j + columnRadius p) : i = j := by
  have hmargin := p.outer_distance
  have hr : 2 * columnRadius p < p.D := by dsimp [columnRadius]; omega
  by_contra h
  rcases lt_or_gt_of_ne h with h | h
  · have := axis_spacing p h; omega
  · have := axis_spacing p h; omega

private theorem column_inside (p : Scales.Parameters) {i x : ℕ} (hi : i < p.axes)
    (hx : p.x i - columnRadius p ≤ x ∧ x ≤ p.x i + columnRadius p) : 0 < x ∧ x < p.W := by
  have hl := readLength_add_lt_x p i p.levels
  have hr := x_add_readLength_lt_W p hi p.levels
  rw [readLength_eq p p.levels_pos (le_refl _)] at hl hr
  dsimp only [columnRadius] at hx
  omega

private theorem endpoint_columns_span (p : Scales.Parameters) (e : Endpoint) {x : ℕ}
    (hx : x ∈ endpointColumns p e) :
    p.x e.port - columnRadius p ≤ x ∧ x ≤ p.x e.port + columnRadius p := by
  have hL : (coordinates p).length e.level ≤ p.L p.levels := readLength_le_last p e.level
  have hmargin : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  change (coordinates p).x e.port - columnRadius p ≤ x ∧ x ≤ (coordinates p).x e.port + columnRadius p
  cases hd : e.inward <;>
    simp [endpointColumns, auxiliary, outward, inward, hd] at hx <;> dsimp [columnRadius] <;> omega

private theorem center_columns_span (p : Scales.Parameters) (i : ℕ) {x : ℕ}
    (hx : x ∈ centerColumns p i) :
    p.x i - columnRadius p ≤ x ∧ x ≤ p.x i + columnRadius p := by
  change (coordinates p).x i - columnRadius p ≤ x ∧ x ≤ (coordinates p).x i + columnRadius p
  simp only [centerColumns, specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hx
  dsimp [columnRadius]
  omega

private theorem endpoint_columns_nodup (p : Scales.Parameters) (e : Endpoint)
    (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels) : (endpointColumns p e).Nodup := by
  have hL : 16384 ≤ (coordinates p).length e.level := readLength_ge p hj hm
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  cases hd : e.inward <;> simp [endpointColumns, auxiliary, outward, inward, hd] <;> omega

private theorem center_columns_nodup (p : Scales.Parameters) (i : ℕ) : (centerColumns p i).Nodup := by
  have hx : 64 < (coordinates p).x i := by
    change 64 < p.x i
    have := readLength_add_lt_x p i 0; omega
  simp [centerColumns, specialColumns]
  omega

private def middleList : Group → List ℕ
  | .wire _ _ => []
  | .triple a => [a + 1]

private theorem centers_nodup (l : PortLayout) (hl : l.pages.Valid) : (centers l).Nodup := by
  have heq : centers l = l.pages.lowerPage.groups.flatMap middleList := by
    simp only [centers, pages, Pages.lowerPage, List.flatMap_map, List.filterMap_eq_flatMap_toList]
    apply List.flatMap_congr
    intro g _
    cases g <;> rfl
  rw [heq]
  apply List.nodup_flatMap.mpr
  constructor
  · intro g _; cases g <;> simp [middleList]
  · apply page_parts_pairwise _ hl.lower middleList
    intro g k hk
    cases g <;> simp [middleList, Group.ports] at hk ⊢
    exact Or.inr (Or.inl hk)

private theorem endpoint_flat_nodup (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (side : Side) :
    ((l.endpoints.filter fun e => decide (e.side = side)).flatMap (endpointColumns p)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro e he
    obtain ⟨hj, hm⟩ := l.endpoints_level_bounds p hl hM (List.mem_filter.mp he).1
    exact endpoint_columns_nodup p e hj hm
  · refine List.Pairwise.imp_of_mem (fun {e f} he hf hne => ?_) ((l.endpoints_nodup hl).filter _)
    apply List.disjoint_left.mpr
    intro x heCol hfCol
    have hport := column_owner p (endpoint_columns_span p e heCol) (endpoint_columns_span p f hfCol)
    have heSide := of_decide_eq_true (List.mem_filter.mp he).2
    have hfSide := of_decide_eq_true (List.mem_filter.mp hf).2
    exact hne (l.endpoints_key_injective hl (List.mem_filter.mp he).1 (List.mem_filter.mp hf).1
      (heSide.trans hfSide.symm) hport)

private theorem center_flat_nodup (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid) :
    ((centers l).flatMap (centerColumns p)).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · exact fun i _ => center_columns_nodup p i
  · refine List.Pairwise.imp_of_mem (fun {i j} _ _ hne => ?_) (centers_nodup l hl)
    apply List.disjoint_left.mpr
    intro x hi hj
    exact hne (column_owner p (center_columns_span p i hi) (center_columns_span p j hj))

private theorem page_parts_disjoint (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (side : Side) :
    List.Disjoint ((l.endpoints.filter fun e => decide (e.side = side)).flatMap (endpointColumns p))
      (if side = .lower then (centers l).flatMap (centerColumns p) else []) := by
  apply List.disjoint_left.mpr
  intro x he hc
  split at hc
  · rename_i hs
    obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp he
    obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hc
    have hport := column_owner p (endpoint_columns_span p e hxe) (center_columns_span p i hxi)
    obtain ⟨kind, first, hg, hmiddle⟩ := center_gate_mem l hi
    have heSide : e.side = .lower := (of_decide_eq_true (List.mem_filter.mp he).2).trans hs
    exact l.endpoints_lower_ne_gate_middle hl hg (List.mem_filter.mp he).1 heSide (hport.trans hmiddle)
  · cases hc

private theorem page_interior_bounds (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) (side : Side) {x : ℕ}
    (hx : x ∈ ((l.endpoints.filter fun e => decide (e.side = side)).flatMap (endpointColumns p) ++
      if side = .lower then (centers l).flatMap (centerColumns p) else [])) : 0 < x ∧ x < p.W := by
  rcases List.mem_append.mp hx with he | hc
  · obtain ⟨e, he, hxe⟩ := List.mem_flatMap.mp he
    exact column_inside p (lt_of_lt_of_le (l.endpoints_port_lt hl (List.mem_filter.mp he).1) ha)
      (endpoint_columns_span p e hxe)
  · split at hc
    · obtain ⟨i, hi, hxi⟩ := List.mem_flatMap.mp hc
      exact column_inside p (center_port l p hl ha hi) (center_columns_span p i hxi)
    · cases hc

/-- Every actual page column occurs once, including the two frame columns. -/
theorem pageColumnCoordinates_nodup (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes) (side : Side) :
    (l.pageColumnCoordinates p side).Nodup := by
  change ([0, p.W] ++ _ ++ _).Nodup
  rw [List.append_assoc]
  have hE := endpoint_flat_nodup l p hl hM side
  have hG : (if side = .lower then (centers l).flatMap (centerColumns p) else []).Nodup := by
    split
    · exact center_flat_nodup l p hl
    · exact List.nodup_nil
  have hI := hE.append hG (page_parts_disjoint l p hl side)
  refine List.Nodup.append ?_ hI ?_
  · have hW := x_add_readLength_lt_W p p.axes_pos 0
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, List.nodup_nil,
      not_false_eq_true, and_true]
    omega
  · apply List.disjoint_left.mpr
    intro x hx hI
    have hb := page_interior_bounds l p hl ha side hI
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    omega

end PushPuzzle.PushS.PortLayout

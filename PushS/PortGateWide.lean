/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortGatePageWindow
import all PushS.PortGatePageWindow
import all PushS.PortEndpointWide
import all PushS.PortWideGeometry
import all PushS.PortTwoPageStreets
import all PushS.PortSegmentBounds
import all PushS.PortStreetEnumeration
import all PushS.PortStreetSeparation
import all PushS.PortSegments

/-! Actual wide anchors on the two sides of a gate's bottom work row. -/

public section
namespace PushPuzzle.PushS.PortLayout


open PushFS PushFS.Reduction

/-- A physical wide separator beyond the leftmost or rightmost special gate column. -/
structure GateWideSeparator (l : PortLayout) (p : Scales.Parameters) (middle : ℕ) (right : Bool) where
  /-- Actual finite emitted cell. -/
  cell : Cell (p.W + 1) (p.H + 1)
  /-- Membership after conditional even rounding. -/
  hole : cell ∈ l.wideSeparatorHoles p
  /-- The depth-plus-two bottom work row. -/
  row : cell.2.val = p.H - (readDepth p 1 + 2)
  /-- Beyond the extreme special column on its selected side. -/
  outside : if right then p.x middle + 12 < cell.1.val else cell.1.val < p.x middle - 2
  /-- Only this gate's special streets occur between its axis and the separator. -/
  columns : ∀ z ∈ l.pageColumnCoordinates p .lower,
    (if right then p.x middle < z ∧ z ≤ cell.1.val else cell.1.val ≤ z ∧ z < p.x middle) →
    z ∈ gateSpecialColumns p middle

private theorem gate_gap (l : PortLayout) (p : Scales.Parameters) (hl : l.pages.Valid)
    (ha : l.portCount ≤ p.axes) {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) (right : Bool) :
    ∃ a b, (a, b) ∈ adjacentPairs (l.pageColumnCoordinates p .lower) ∧
      p.L p.levels < b - a ∧ (if right then a = p.x middle + 12 else b = p.x middle - 2) := by
  have hc : (coordinates p).x = p.x := rfl
  have hleft := readLength_add_lt_x p middle p.levels
  have hright := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) p.levels
  rw [readLength_eq p p.levels_pos le_rfl] at hleft hright
  cases right with
  | false =>
    have hext : p.x middle - 2 ∈ l.pageColumnCoordinates p .lower :=
      l.gateSpecialColumn_mem_page p hi (by simp [gateSpecialColumns, specialColumns, hc])
    have hzero : 0 ∈ l.pageColumnCoordinates p .lower := by simp [pageColumnCoordinates, pageColumns]
    obtain ⟨a, hab⟩ := previous_column _ hext ⟨0, hzero, by omega⟩
    have hg := (adjacentPair_gap hab).1
    have ha' := (adjacentPair_mem hab).1
    refine ⟨a, p.x middle - 2, hab, ?_, rfl⟩
    by_contra h
    have hnear : Nat.dist a (p.x middle) ≤ p.L p.levels + 12 := by simp only [Nat.dist]; omega
    have hc := l.gatePageColumns_near p hl ha hi ha' hnear
    simp only [gateSpecialColumns, specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
    change a = p.x middle ∨ a = p.x middle - 2 ∨ a = p.x middle + 4 ∨
      a = p.x middle + 6 ∨ a = p.x middle + 8 ∨ a = p.x middle + 12 at hc
    omega
  | true =>
    have hext : p.x middle + 12 ∈ l.pageColumnCoordinates p .lower :=
      l.gateSpecialColumn_mem_page p hi (by simp [gateSpecialColumns, specialColumns, hc])
    have hframe : p.W ∈ l.pageColumnCoordinates p .lower := by
      simp [pageColumnCoordinates, pageColumns, show (coordinates p).W = p.W from rfl]
    obtain ⟨b, hab⟩ := next_column _ hext ⟨p.W, hframe, by omega⟩
    have hg := (adjacentPair_gap hab).1
    have hb := (adjacentPair_mem hab).2
    refine ⟨p.x middle + 12, b, hab, ?_, rfl⟩
    by_contra h
    have hnear : Nat.dist b (p.x middle) ≤ p.L p.levels + 12 := by simp only [Nat.dist]; omega
    have hc := l.gatePageColumns_near p hl ha hi hb hnear
    simp only [gateSpecialColumns, specialColumns, List.mem_cons, List.not_mem_nil, or_false] at hc
    change b = p.x middle ∨ b = p.x middle - 2 ∨ b = p.x middle + 4 ∨
      b = p.x middle + 6 ∨ b = p.x middle + 8 ∨ b = p.x middle + 12 at hc
    omega

private theorem gate_branch_uncrossed (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (a b : ℕ) :
    crosses l (coordinates p) .lower a b (readDepth p 1 + 2) = false := by
  apply Bool.eq_false_iff.mpr
  intro hcross
  obtain ⟨g, hg, hcross⟩ := List.any_eq_true.mp hcross
  have hrow := (of_decide_eq_true hcross).2.1
  change readDepth p g.level = readDepth p 1 + 2 at hrow
  have hb := placement_level_bounds l hl hg
  by_cases hlevel : g.level = 1
  · simp only [hlevel] at hrow
    omega
  · have hg := depth_gap p (show 1 ≤ 1 by omega) (show 1 < g.level by omega) (hb.2.trans hM)
    omega

/-- Both sides of every actual gate have physical wide separators on its bottom work row. -/
theorem gateWideSeparator_nonempty (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (hM : l.pages.highest ≤ p.levels) (ha : l.portCount ≤ p.axes)
    {middle : ℕ} (hi : middle ∈ l.gateCenterCoordinates) (right : Bool) :
    Nonempty (GateWideSeparator l p middle right) := by
  obtain ⟨a, b, hab, hwide, hext⟩ := gate_gap l p hl ha hi right
  obtain ⟨g, hhole, hrow, hgl, hgr⟩ := wide_cell_of_uncrossed l p hl ha .lower
    ((l.workingDepthCoordinates_mem p 0 (by have := p.levels_pos; omega)).2)
    hab hwide (gate_branch_uncrossed l p hl hM a b)
  refine ⟨⟨g, hhole, hrow, ?_, ?_⟩⟩
  · cases right <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hext ⊢ <;> omega
  · intro z hz hzin
    have hno := (adjacentPair_gap hab).2 z hz
    have hnear : Nat.dist z (p.x middle) ≤ p.L p.levels + 12 := by
      cases hr : right <;> simp only [hr, Bool.false_eq_true, ite_true, ite_false] at hext hzin <;>
        simp only [Nat.dist] <;> omega
    have hc := l.gatePageColumns_near p hl ha hi hz hnear
    rcases List.mem_cons.mp hc with haxis | hspecial
    · cases right <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hzin <;> omega
    · exact hspecial

/-- An axis-far cell between a gate axis and either actual separator is far from every axis. -/
theorem gateWideSeparator_interval_far_axes (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {right : Bool} (g : GateWideSeparator l p middle right)
    {x : ℕ} (hbetween : if right then p.x middle < x ∧ x ≤ g.cell.1.val
      else g.cell.1.val ≤ x ∧ x < p.x middle)
    (hfar : p.L p.levels + 16 < Nat.dist x (p.x middle)) :
    ∀ i < l.portCount, p.L p.levels + 12 < Nat.dist x (p.x i) := by
  intro i hiport
  have hm := x_add_readLength_lt_W p (hiport.trans_le ha) 0
  let col : Fin (p.W + 1) := ⟨p.x i, by omega⟩
  have hc : col ∈ l.streetColumnSet p := axis_in_streetColumns l p hiport
  have hwide := l.wideSeparatorHoles_street_gap p hl g.hole col hc
  have hb : p.L p.levels + 16 < 2 * p.b p.levels + 2 := by
    have ht := Nat.mul_le_mul_right (p.Y p.levels + p.L p.levels + 10)
      (show 1 ≤ 8 * (p.axes + 1) by omega)
    simp only [Nat.one_mul] at ht
    unfold Scales.Parameters.b
    omega
  have hno : ¬(if right then p.x middle < p.x i ∧ p.x i ≤ g.cell.1.val
      else g.cell.1.val ≤ p.x i ∧ p.x i < p.x middle) := by
    intro hin
    have hm := l.gateSpecialColumn_not_main p hl ha hi (x := col)
      (g.columns (p.x i) (axis_in_pageColumns l p hl .lower hiport) hin)
    exact hm ((l.mainColumnSet_iff p col).mpr (Or.inr (Or.inr ⟨i, hiport, rfl⟩)))
  cases right <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hno hbetween <;>
    simp only [Nat.dist, col] at hfar hwide ⊢ <;> omega

/-- The finite row interval from a gate axis to its actual separator stays off the frame. -/
theorem gateWideSeparator_interval_off_frame (l : PortLayout) (p : Scales.Parameters)
    (hl : l.pages.Valid) (ha : l.portCount ≤ p.axes) {middle : ℕ}
    (hi : middle ∈ l.gateCenterCoordinates) {right : Bool} (g : GateWideSeparator l p middle right)
    {q : Cell (p.W + 1) (p.H + 1)} (hy : q.2.val = p.H - (readDepth p 1 + 2))
    (hx : if right then p.x middle < q.1.val ∧ q.1.val ≤ g.cell.1.val
      else g.cell.1.val ≤ q.1.val ∧ q.1.val < p.x middle) : q ∉ Boundary.frame := by
  have hg := l.wideSeparatorHoles_off_frame p hl g.hole
  have hx0 := readLength_add_lt_x p middle 0
  have hxW := x_add_readLength_lt_W p ((gate_center_lt l hl hi).trans_le ha) 0
  have hY := readDepth_add_lt_H p 1
  cases right <;> simp only [Bool.false_eq_true, ite_true, ite_false] at hx
  all_goals
    simp only [Boundary.frame, Boundary.edge, Finset.mem_union, Finset.mem_filter,
      Finset.mem_univ, true_and] at hg ⊢
    omega

end PushPuzzle.PushS.PortLayout

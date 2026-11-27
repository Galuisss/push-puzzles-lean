/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombPreprocess
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int.Binary

/-! Exact integral intersections of the prepared comb segments with integer tooth columns. -/

public section

namespace PushPuzzle.PushS.Comb


open Cslib.Orthogonal Turing.MultiTapeTM

/-- Height of a horizontal or slope-one prepared segment at the supplied integer column. -/
@[expose] def cutHeight (a b : Point) (column : ℤ) : ℤ :=
  if a.2 = b.2 then a.2 else column + a.2 - a.1

/-- The actual integral cut point computed by the contour scanner. -/
@[expose] def cutPoint (a b : Point) (column : ℤ) : Point := (column, cutHeight a b column)

private noncomputable def lineGraph (m c : ℝ) : ℝ →ᵃ[ℝ] (ℝ × ℝ) :=
  (AffineMap.id ℝ ℝ).prod ((m • AffineMap.id ℝ ℝ) + AffineMap.const ℝ ℝ c)

private theorem graph_segment (m c a b : ℝ) :
    _root_.segment ℝ (a, m * a + c) (b, m * b + c) =
      (fun x : ℝ => (x, m * x + c)) '' _root_.segment ℝ a b := by
  have h := image_segment ℝ (lineGraph m c) a b
  change (fun x : ℝ => (x, m * x + c)) '' _root_.segment ℝ a b =
    _root_.segment ℝ (a, m * a + c) (b, m * b + c) at h
  exact h.symm

private theorem mem_slope_segment (a b : Point) (m c : ℝ)
    (ha : (a.2 : ℝ) = m * a.1 + c) (hb : (b.2 : ℝ) = m * b.1 + c) (p : ℝ × ℝ) :
    p ∈ segment a b ↔ p.2 = m * p.1 + c ∧
      min (a.1 : ℝ) b.1 ≤ p.1 ∧ p.1 ≤ max (a.1 : ℝ) b.1 := by
  change p ∈ _root_.segment ℝ ((a.1 : ℝ), (a.2 : ℝ)) ((b.1 : ℝ), (b.2 : ℝ)) ↔ _
  rw [ha, hb, graph_segment, _root_.segment_eq_Icc']
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨rfl, hx⟩
  · rintro ⟨hy, hx⟩
    exact ⟨p.1, hx, Prod.ext rfl hy.symm⟩

/-- Full real segment membership on a tooth column is exactly the computed integer height
and the closed horizontal endpoint interval. -/
theorem segment_column_iff (a b : Point)
    (hshape : a.2 = b.2 ∨ a.2 - a.1 = b.2 - b.1) (column : ℤ)
    (p : ℝ × ℝ) (hx : p.1 = column) :
    p ∈ segment a b ↔ p.2 = (cutHeight a b column : ℝ) ∧
      min a.1 b.1 ≤ column ∧ column ≤ max a.1 b.1 := by
  have hbounds : (min (a.1 : ℝ) b.1 ≤ p.1 ∧ p.1 ≤ max (a.1 : ℝ) b.1) ↔
      min a.1 b.1 ≤ column ∧ column ≤ max a.1 b.1 := by
    rw [hx]
    exact_mod_cast Iff.rfl
  by_cases hh : a.2 = b.2
  · rw [mem_slope_segment a b 0 a.2 (by simp) (by simpa only [zero_mul, zero_add] using congrArg (fun z : ℤ => (z : ℝ)) hh.symm)]
    simp only [cutHeight, hh, ite_true, zero_mul, zero_add, hbounds]
  · have hs := hshape.resolve_left hh
    have hs' : (a.2 : ℝ) - a.1 = (b.2 : ℝ) - b.1 := by exact_mod_cast hs
    rw [mem_slope_segment a b 1 ((a.2 : ℝ) - a.1) (by ring) (by linarith)]
    apply and_congr _ hbounds
    simp only [cutHeight, hh, ite_false, Int.cast_sub, Int.cast_add, one_mul, hx]
    ring_nf

/-- The scanner's integral cut point lies on the full actual segment whenever its column is between the endpoints. -/
theorem cutPoint_mem_segment (a b : Point)
    (hshape : a.2 = b.2 ∨ a.2 - a.1 = b.2 - b.1) (column : ℤ)
    (hx : min a.1 b.1 ≤ column ∧ column ≤ max a.1 b.1) :
    realPoint (cutPoint a b column) ∈ segment a b := by
  exact (segment_column_iff a b hshape column (realPoint (cutPoint a b column)) rfl).mpr ⟨rfl, hx⟩

/-- Each real segment has at most the one computed cut point on a given contour tooth. -/
theorem eq_cutPoint_of_mem_segment (a b : Point)
    (hshape : a.2 = b.2 ∨ a.2 - a.1 = b.2 - b.1) (column : ℤ)
    {p : ℝ × ℝ} (hp : p ∈ segment a b) (hx : p.1 = column) :
    p = realPoint (cutPoint a b column) := by
  have hy := ((segment_column_iff a b hshape column p hx).mp hp).1
  exact Prod.ext hx hy

/-- Computing a cut height uses only standard binary signed-integer arithmetic. -/
@[fun_prop] theorem computableInPolyTime_cutHeight :
    ComputableInPolyTime (fun p : (Point × Point) × ℤ => cutHeight p.1.1 p.1.2 p.2)
      (encPair (encPair encPoint encPoint) encIntBin) encIntBin := by
  unfold cutHeight encPoint
  fun_prop

/-- Computing the actual cut point preserves the standard point encoding. -/
@[fun_prop] theorem computableInPolyTime_cutPoint :
    ComputableInPolyTime (fun p : (Point × Point) × ℤ => cutPoint p.1.1 p.1.2 p.2)
      (encPair (encPair encPoint encPoint) encIntBin) encPoint := by
  unfold cutPoint encPoint
  have hheight := computableInPolyTime_cutHeight
  unfold encPoint at hheight
  fun_prop

end PushPuzzle.PushS.Comb

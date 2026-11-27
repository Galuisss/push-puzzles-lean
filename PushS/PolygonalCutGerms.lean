/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import CslibFrontier.Foundations.Geometry.Polygonal.CutTransport
public import PushS.PolygonalSubroute

/-! Actual affine cut refinement retains each original outgoing ray with a positive scale. -/

public section
namespace PushPuzzle.Polygonal.Route

open Cslib

open Cslib.Polygonal Cslib.Polygonal.Route


private theorem germ_mapAtCuts_start (p : Route) (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ) :
    ∃ scale : ℝ, 0 < scale ∧ (p.mapAtCuts levels coordinate id).germ false = scale • p.germ false := by
  let q := p.mapAtCuts levels coordinate id
  obtain ⟨j, a, b, ha, hab, _, _, h⟩ := eval_mapAtCuts (S := levels) (c := coordinate) (F := id)
    (fun _ _ _ _ _ => rfl) p (0 : Fin q.segments)
  have hend := ((h 0 ⟨le_rfl, zero_le_one⟩).2 false).mp (by
    simp only [AtEnd, position, Fin.val_zero, Nat.cast_zero, add_zero, Bool.false_eq_true, ite_false])
  simp only [AffineMap.lineMap_apply_zero, AtEnd, position, Bool.false_eq_true, ite_false] at hend
  have hjval : j.val = 0 := by
    have hnonneg := Nat.cast_nonneg (α := ℝ) j.val
    have hjreal : (j.val : ℝ) = 0 := by linarith
    exact_mod_cast hjreal
  have ha0 : a = 0 := by simp only [hjval, Nat.cast_zero, zero_add] at hend; exact hend
  have hj : j = 0 := Fin.ext hjval
  subst j
  subst a
  have hzero := (h 0 ⟨le_rfl, zero_le_one⟩).1
  have hone := (h 1 ⟨zero_le_one, le_rfl⟩).1
  change q.eval 0 0 = _ at hzero
  change q.eval 0 1 = _ at hone
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, id_eq] at hzero hone
  change q.point 0 = p.point 0 at hzero
  refine ⟨b, hab, ?_⟩
  change q.point (0 : Fin q.segments).succ - q.point 0 =
    b • (p.point (0 : Fin p.segments).succ - p.point 0)
  rw [hone, hzero]
  simp only [AffineMap.lineMap_apply_module', Fin.castSucc_zero, add_sub_cancel_right]

private theorem germ_mapAtCuts_finish (p : Route) (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ) :
    ∃ scale : ℝ, 0 < scale ∧ (p.mapAtCuts levels coordinate id).germ true = scale • p.germ true := by
  let q := p.mapAtCuts levels coordinate id
  obtain ⟨j, a, b, _, hab, hb, _, h⟩ := eval_mapAtCuts (S := levels) (c := coordinate) (F := id)
    (fun _ _ _ _ _ => rfl) p (Fin.last q.bends)
  have hend := ((h 1 ⟨zero_le_one, le_rfl⟩).2 true).mp (by
    change q.AtEnd (Fin.last q.bends) 1 true
    simp only [AtEnd, position, Fin.val_last, segments, Nat.cast_add, Nat.cast_one, ite_true])
  simp only [AffineMap.lineMap_apply_one, AtEnd, position, ite_true] at hend
  have hjle : (j.val : ℝ) + 1 ≤ p.segments := by exact_mod_cast j.isLt
  have hb1 : b = 1 := by linarith
  have hjval : j.val = p.bends := by
    have heq : (j.val : ℝ) = p.bends := by simp only [segments, Nat.cast_add, Nat.cast_one] at hend; linarith
    exact_mod_cast heq
  have hj : j = Fin.last p.bends := Fin.ext hjval
  subst j
  subst b
  have hzero := (h 0 ⟨le_rfl, zero_le_one⟩).1
  have hone := (h 1 ⟨zero_le_one, le_rfl⟩).1
  change q.eval (Fin.last q.bends) 0 = _ at hzero
  change q.eval (Fin.last q.bends) 1 = _ at hone
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, id_eq] at hzero hone
  refine ⟨1 - a, by linarith, ?_⟩
  change q.point (Fin.last q.bends).castSucc - q.point (Fin.last q.bends).succ =
    (1 - a) • (p.point (Fin.last p.bends).castSucc - p.point (Fin.last p.bends).succ)
  rw [hzero, hone]
  simp only [AffineMap.lineMap_apply_module, smul_sub, sub_smul, one_smul]
  abel

/-- Refinement at actual affine coordinate cuts preserves every source endpoint's outgoing direction. -/
theorem germ_mapAtCuts_id (p : Route) (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ) (side : Bool) :
    ∃ scale : ℝ, 0 < scale ∧ (p.mapAtCuts levels coordinate id).germ side = scale • p.germ side := by
  cases side
  · exact germ_mapAtCuts_start p levels coordinate
  · exact germ_mapAtCuts_finish p levels coordinate

/-- Actual affine cut refinement retains the real argument of each original endpoint ray. -/
theorem arg_germ_mapAtCuts_id (p : Route) (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ) (side : Bool) :
    ((p.mapAtCuts levels coordinate id).germ side).arg = (p.germ side).arg := by
  obtain ⟨scale, hscale, he⟩ := germ_mapAtCuts_id p levels coordinate side
  rw [he]
  exact Complex.arg_real_mul _ hscale

/-- A consecutive fragment starting at the original source start retains the exact original first germ. -/
theorem germ_subroute_start (p : Route) (last : Fin (p.bends + 2)) (hlt : 0 < last) :
    ((PushPuzzle.Polygonal.Route.subroute p) 0 last hlt).germ false = p.germ false := by
  rfl

/-- A consecutive fragment ending at the original source finish retains the exact original last germ. -/
theorem germ_subroute_finish (p : Route) (first : Fin (p.bends + 2)) (hlt : first < Fin.last (p.bends + 1)) :
    ((PushPuzzle.Polygonal.Route.subroute p) first (Fin.last (p.bends + 1)) hlt).germ true = p.germ true := by
  simp only [germ, ite_true, subroute, finish, segments]
  apply congrArg₂ (fun a b : ℂ => a - b)
  · apply congrArg p.point
    apply Fin.ext
    simp only [Fin.val_castSucc, Fin.val_last]
    have hl : first.val < p.bends + 1 := hlt
    omega
  · apply congrArg p.point
    apply Fin.ext
    simp only [Fin.val_last]
    have hl : first.val < p.bends + 1 := hlt
    omega

end PushPuzzle.Polygonal.Route

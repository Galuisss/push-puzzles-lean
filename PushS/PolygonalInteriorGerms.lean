/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PolygonalCutGerms

/-! Actual cut-end rays at a strict original segment point retain that original segment's direction. -/

public section
namespace PushPuzzle.Polygonal.Route

open Cslib

open Cslib.Polygonal Cslib.Polygonal.Route


private theorem index_eq_of_interior_position (p : Route) (left right : Fin p.segments) {s t : ℝ}
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Ioo 0 1) (he : p.position left s = p.position right t) :
    left = right ∧ s = t := by
  have hindex : left.val = right.val := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · have hle : (left.val : ℝ) + 1 ≤ right.val := by exact_mod_cast hlt
      simp only [position] at he
      linarith [hs.2, ht.1]
    · have hle : (right.val : ℝ) + 1 ≤ left.val := by exact_mod_cast hgt
      simp only [position] at he
      linarith [hs.1, ht.2]
  have hi : left = right := Fin.ext hindex
  refine ⟨hi, ?_⟩
  simp only [position, hi] at he
  linarith

private theorem eval_sub (p : Route) (i : Fin p.segments) (s t : ℝ) :
    p.eval i s - p.eval i t = (s - t) • (p.point i.succ - p.point i.castSucc) := by
  simp only [eval, AffineMap.lineMap_apply_module', sub_smul]
  abel

/-- A genuine refined segment ending at a strict original segment point has the same outgoing ray. -/
theorem segment_germ_mapAtCuts_interior {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish)
    (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ)
    (segment : Fin (p.mapAtCuts levels coordinate id).segments) (side : Bool)
    (original : Fin p.segments) {parameter : ℝ} (ht : parameter ∈ Set.Ioo 0 1)
    (he : (p.mapAtCuts levels coordinate id).eval segment (if side then 1 else 0) = p.eval original parameter) :
    ∃ scale : ℝ, 0 < scale ∧
      (if side then (p.mapAtCuts levels coordinate id).eval segment 0 - (p.mapAtCuts levels coordinate id).eval segment 1
       else (p.mapAtCuts levels coordinate id).eval segment 1 - (p.mapAtCuts levels coordinate id).eval segment 0) =
        scale • (if side then p.point original.castSucc - p.point original.succ
          else p.point original.succ - p.point original.castSucc) := by
  obtain ⟨old, a, b, ha, hab, hb, _, h⟩ := eval_mapAtCuts (S := levels) (c := coordinate) (F := id)
    (fun _ _ _ _ _ => rfl) p segment
  have hzero := (h 0 ⟨le_rfl, zero_le_one⟩).1
  have hone := (h 1 ⟨zero_le_one, le_rfl⟩).1
  simp only [AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, id_eq] at hzero hone
  cases side with
  | false =>
    have hpos := hp.position_eq_of_eval_eq hne old original ⟨ha, hab.le.trans hb⟩ ⟨ht.1.le, ht.2.le⟩ (hzero.symm.trans he)
    obtain ⟨rfl, rfl⟩ := index_eq_of_interior_position p old original ⟨ha, hab.le.trans hb⟩ ht hpos
    refine ⟨b - a, sub_pos.mpr hab, ?_⟩
    simp only [Bool.false_eq_true, ite_false]
    rw [hone, hzero, eval_sub]
  | true =>
    have hpos := hp.position_eq_of_eval_eq hne old original ⟨ha.trans hab.le, hb⟩ ⟨ht.1.le, ht.2.le⟩ (hone.symm.trans he)
    obtain ⟨rfl, rfl⟩ := index_eq_of_interior_position p old original ⟨ha.trans hab.le, hb⟩ ht hpos
    refine ⟨b - a, sub_pos.mpr hab, ?_⟩
    simp only [ite_true]
    rw [hzero, hone, eval_sub]
    simp only [sub_smul, smul_sub]
    abel

/-- A true source subroute at an interior cut keeps the corresponding original outgoing segment ray. -/
theorem subroute_germ_mapAtCuts_interior {p : Route} (hp : p.IsSimple) (hne : p.start ≠ p.finish)
    (levels : Finset ℝ) (coordinate : ℂ →ᵃ[ℝ] ℝ)
    (first last : Fin ((p.mapAtCuts levels coordinate id).bends + 2)) (hlt : first < last) (side : Bool)
    (original : Fin p.segments) {parameter : ℝ} (ht : parameter ∈ Set.Ioo 0 1)
    (he : ((PushPuzzle.Polygonal.Route.subroute (p.mapAtCuts levels coordinate id)) first last hlt).endpoint side = p.eval original parameter) :
    ∃ scale : ℝ, 0 < scale ∧ ((PushPuzzle.Polygonal.Route.subroute (p.mapAtCuts levels coordinate id)) first last hlt).germ side =
      scale • (if side then p.point original.castSucc - p.point original.succ
        else p.point original.succ - p.point original.castSucc) := by
  let q := p.mapAtCuts levels coordinate id
  let fragment := (PushPuzzle.Polygonal.Route.subroute q) first last hlt
  let segment : Fin fragment.segments := if side then Fin.last fragment.bends else 0
  have hend : fragment.eval segment (if side then 1 else 0) = fragment.endpoint side := by
    cases side <;> simp [segment, eval, endpoint, start, finish]
  have hpoint : q.eval ((PushPuzzle.Polygonal.Route.subrouteIndex q) first last hlt segment) (if side then 1 else 0) = p.eval original parameter :=
    (eval_subroute q first last hlt segment _).symm.trans (hend.trans he)
  obtain ⟨scale, hscale, hg⟩ := segment_germ_mapAtCuts_interior hp hne levels coordinate
    ((PushPuzzle.Polygonal.Route.subrouteIndex q) first last hlt segment) side original ht hpoint
  refine ⟨scale, hscale, ?_⟩
  have hexpr : fragment.germ side =
      if side then fragment.eval segment 0 - fragment.eval segment 1
      else fragment.eval segment 1 - fragment.eval segment 0 := by
    cases side <;> simp [segment, germ, eval, start, finish]
  rw [show ((PushPuzzle.Polygonal.Route.subroute (p.mapAtCuts levels coordinate id)) first last hlt).germ side = fragment.germ side from rfl, hexpr]
  dsimp only [fragment]
  simp only [eval_subroute]
  exact hg

end PushPuzzle.Polygonal.Route

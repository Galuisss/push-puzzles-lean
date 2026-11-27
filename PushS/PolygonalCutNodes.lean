/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PolygonalSubroute
public import CslibFrontier.Foundations.Geometry.Polygonal.CutTransport
import all CslibFrontier.Foundations.Geometry.Polygonal.CutTransport

/-! Actual cut levels become listed nodes of the existing exact polygonal refinement. -/

public section
namespace PushPuzzle.Polygonal.Route

open Cslib

open Cslib.Polygonal Cslib.Polygonal.Route


private theorem coordinate_eval (p : Route) (c : ℂ →ᵃ[ℝ] ℝ) (i : Fin p.segments) (t : ℝ) :
    c (p.eval i t) = AffineMap.lineMap (c (p.point i.castSucc)) (c (p.point i.succ)) t :=
  AffineMap.apply_lineMap c _ _ _

/-- Affine images retain nonconstant target coordinates on every exact refinement segment. -/
theorem coordinate_mapAtCuts_affine_ne (p : Route) (levels : Finset ℝ)
    (cut target : ℂ →ᵃ[ℝ] ℝ) (f : ℂ →ᵃ[ℝ] ℂ)
    (hne : ∀ i : Fin p.segments, target (f (p.point i.castSucc)) ≠ target (f (p.point i.succ)))
    (i : Fin (p.mapAtCuts levels cut f).segments) :
    target ((p.mapAtCuts levels cut f).point i.castSucc) ≠
      target ((p.mapAtCuts levels cut f).point i.succ) := by
  obtain ⟨j, a, b, _, hab, _, _, h⟩ := eval_mapAtCuts (S := levels) (c := cut) (F := f)
    (fun a b _ t _ => AffineMap.apply_lineMap f a b t) p i
  have hl := (h 0 ⟨le_rfl, zero_le_one⟩).1
  have hr := (h 1 ⟨zero_le_one, le_rfl⟩).1
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one] at hl hr
  rw [hl, hr]
  change (target.comp f) (AffineMap.lineMap (p.point j.castSucc) (p.point j.succ) a) ≠
    (target.comp f) (AffineMap.lineMap (p.point j.castSucc) (p.point j.succ) b)
  rw [AffineMap.apply_lineMap, AffineMap.apply_lineMap]
  exact fun he => (ne_of_lt hab) (AffineMap.lineMap_injective ℝ (hne j) he)

private theorem unit_level_endpoint {a b t : ℝ} (hab : a ≠ b) (ht : t ∈ Set.Icc 0 1)
    (hcut : AffineMap.lineMap a b t ∉ Set.Ioo (min a b) (max a b)) : t = 0 ∨ t = 1 := by
  by_contra hn
  have h0 : 0 < t := by simp only [not_or] at hn; exact lt_of_le_of_ne ht.1 (Ne.symm hn.1)
  have h1 : t < 1 := by simp only [not_or] at hn; exact lt_of_le_of_ne ht.2 hn.2
  apply hcut
  rcases lt_or_gt_of_ne hab with h | h
  · rw [min_eq_left h.le, max_eq_right h.le]
    simp only [Set.mem_Ioo, AffineMap.lineMap_apply_ring']
    constructor <;> nlinarith
  · rw [min_eq_right h.le, max_eq_left h.le]
    simp only [Set.mem_Ioo, AffineMap.lineMap_apply_ring']
    constructor <;> nlinarith

/-- Every source support point on a retained affine level is an actual listed refinement node. -/
theorem exists_node_mapAtCuts_of_level (p : Route) (levels : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ)
    (hne : ∀ i : Fin p.segments, c (p.point i.castSucc) ≠ c (p.point i.succ))
    {z : ℂ} (hz : z ∈ p.support) (hlevel : c z ∈ levels) :
    ∃ k : Fin ((p.mapAtCuts levels c id).bends + 2), (p.mapAtCuts levels c id).point k = z := by
  let q := p.mapAtCuts levels c id
  have hsupport := support_mapAtCuts (S := levels) (c := c) (F := id) (fun _ _ _ _ _ => rfl) p
  have hzq : z ∈ q.support := by
    change z ∈ (p.mapAtCuts levels c id).support
    rw [hsupport, Set.image_id]
    exact hz
  obtain ⟨i, t, ht, he⟩ := (q.mem_support_iff z).mp hzq
  obtain ⟨j, a, b, _, _, _, hcut, h⟩ := eval_mapAtCuts (S := levels) (c := c) (F := id)
    (fun _ _ _ _ _ => rfl) p i
  have hl := (h 0 ⟨le_rfl, zero_le_one⟩).1
  have hr := (h 1 ⟨zero_le_one, le_rfl⟩).1
  simp only [eval, AffineMap.lineMap_apply_zero, AffineMap.lineMap_apply_one, id_eq] at hl hr
  have hnot : c (q.eval i t) ∉ Set.Ioo (min (c (q.point i.castSucc)) (c (q.point i.succ)))
      (max (c (q.point i.castSucc)) (c (q.point i.succ))) := by
    rw [hl, hr, he]
    exact hcut _ hlevel
  rw [coordinate_eval] at hnot
  rcases unit_level_endpoint (coordinate_mapAtCuts_affine_ne p levels c c (AffineMap.id ℝ ℂ) hne i) ht hnot with rfl | rfl
  · exact ⟨i.castSucc, by simpa only [eval, AffineMap.lineMap_apply_zero] using he⟩
  · exact ⟨i.succ, by simpa only [eval, AffineMap.lineMap_apply_one] using he⟩

/-- A level point of an open simple source route has one exact node index in its refinement. -/
theorem existsUnique_node_mapAtCuts_of_level {p : Route} (hp : p.IsSimple) (hopen : p.start ≠ p.finish)
    (levels : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ)
    (hne : ∀ i : Fin p.segments, c (p.point i.castSucc) ≠ c (p.point i.succ))
    {z : ℂ} (hz : z ∈ p.support) (hlevel : c z ∈ levels) :
    ∃! k : Fin ((p.mapAtCuts levels c id).bends + 2), (p.mapAtCuts levels c id).point k = z := by
  let q := p.mapAtCuts levels c id
  have hq : q.IsSimple := hp.mapAtCuts (S := levels) (c := c) (F := id)
    (fun _ _ _ _ _ => rfl) Function.injective_id
  have hs := endpoint_mapAtCuts (S := levels) (c := c) (F := id) (fun _ _ _ _ _ => rfl) p false
  have ht := endpoint_mapAtCuts (S := levels) (c := c) (F := id) (fun _ _ _ _ _ => rfl) p true
  change q.start = p.start at hs
  change q.finish = p.finish at ht
  have hqo : q.start ≠ q.finish := by simpa only [hs, ht] using hopen
  obtain ⟨k, hk⟩ := exists_node_mapAtCuts_of_level p levels c hne hz hlevel
  refine ⟨k, hk, ?_⟩
  intro j hj
  exact (PushPuzzle.Polygonal.Route.IsSimple.point_injective hq) hqo (hj.trans hk.symm)

private theorem parameter_node_source {p : Route} (hp : p.IsSimple) (hopen : p.start ≠ p.finish)
    (levels : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ)
    (k : Fin ((p.mapAtCuts levels c id).bends + 2)) (i : Fin p.segments) (t : ℝ)
    (ht : t ∈ Set.Icc 0 1) (he : (p.mapAtCuts levels c id).point k = p.eval i t) :
    ((parameterRoute p levels c id).point k).re = p.position i t := by
  induction k using Fin.lastCases with
  | last =>
    let j := Fin.last (p.mapAtCuts levels c id).bends
    obtain ⟨m, a, b, ha, hab, hb, _, hval, hpos⟩ := mapAtCuts_parameter (S := levels) (c := c) (F := id)
      (fun _ _ _ _ _ => rfl) p j
    have hb0 : 0 ≤ b := by linarith
    have hsource : p.eval m b = p.eval i t := by
      calc
        _ = (p.mapAtCuts levels c id).eval j 1 := by
          simpa only [id_eq, AffineMap.lineMap_apply_one] using (hval 1 ⟨zero_le_one, le_rfl⟩).symm
        _ = (p.mapAtCuts levels c id).point (Fin.last _) := by
          change AffineMap.lineMap _ _ (1 : ℝ) = _
          rw [AffineMap.lineMap_apply_one]
          apply congrArg _
          apply Fin.ext
          rfl
        _ = p.eval i t := he
    have hsame := hp.position_eq_of_eval_eq hopen m i ⟨hb0, hb⟩ ht hsource
    have h := hpos 1
    simp only [eval, AffineMap.lineMap_apply_one] at h
    change ((parameterRoute p levels c id).point (Fin.last ((p.mapAtCuts levels c id).bends + 1))).re = p.position m b at h
    rw [hsame] at h
    exact h
  | cast k =>
    obtain ⟨m, a, b, ha, hab, hb, _, hval, hpos⟩ := mapAtCuts_parameter (S := levels) (c := c) (F := id)
      (fun _ _ _ _ _ => rfl) p k
    have ha1 : a ≤ 1 := by linarith
    have hsource : p.eval m a = p.eval i t := by
      calc
        _ = (p.mapAtCuts levels c id).eval k 0 := by
          simpa only [id_eq, AffineMap.lineMap_apply_zero] using (hval 0 ⟨le_rfl, zero_le_one⟩).symm
        _ = (p.mapAtCuts levels c id).point k.castSucc := AffineMap.lineMap_apply_zero _ _
        _ = p.eval i t := he
    have hsame := hp.position_eq_of_eval_eq hopen m i ⟨ha, ha1⟩ ht hsource
    have h := hpos 0
    simp only [eval, AffineMap.lineMap_apply_zero] at h
    change ((parameterRoute p levels c id).point k.castSucc).re = p.position m a at h
    rw [hsame] at h
    exact h

/-- Actual refinement node indices have exactly the order of their original complete route parameters. -/
theorem mapAtCuts_node_order {p : Route} (hp : p.IsSimple) (hopen : p.start ≠ p.finish)
    (levels : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ)
    (a b : Fin ((p.mapAtCuts levels c id).bends + 2))
    (i j : Fin p.segments) (s t : ℝ) (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (ha : (p.mapAtCuts levels c id).point a = p.eval i s)
    (hb : (p.mapAtCuts levels c id).point b = p.eval j t) :
    a < b ↔ p.position i s < p.position j t := by
  have hpa := parameter_node_source hp hopen levels c a i s hs ha
  have hpb := parameter_node_source hp hopen levels c b j t ht hb
  have hmono := parameterRoute_ordered p levels c id
  have ho : a < b ↔ ((parameterRoute p levels c id).point a).re < ((parameterRoute p levels c id).point b).re :=
    hmono.lt_iff_lt.symm
  simpa only [hpa, hpb] using ho

/-- A refinement node at a strict source-segment parameter lies strictly between the two end nodes. -/
theorem mapAtCuts_node_interior {p : Route} (hp : p.IsSimple) (hopen : p.start ≠ p.finish)
    (levels : Finset ℝ) (c : ℂ →ᵃ[ℝ] ℝ) (k : Fin ((p.mapAtCuts levels c id).bends + 2))
    (i : Fin p.segments) (t : ℝ) (ht : t ∈ Set.Ioo 0 1)
    (he : (p.mapAtCuts levels c id).point k = p.eval i t) :
    0 < k ∧ k < Fin.last ((p.mapAtCuts levels c id).bends + 1) := by
  let q := p.mapAtCuts levels c id
  have hs := endpoint_mapAtCuts (S := levels) (c := c) (F := id) (fun _ _ _ _ _ => rfl) p false
  have hf := endpoint_mapAtCuts (S := levels) (c := c) (F := id) (fun _ _ _ _ _ => rfl) p true
  have hstart : q.point 0 = p.eval 0 0 := by
    change q.start = p.start at hs
    simpa only [start, eval, AffineMap.lineMap_apply_zero, Fin.castSucc_zero] using hs
  have hfinish : q.point (Fin.last q.segments) = p.eval (Fin.last p.bends) 1 := by
    change q.finish = p.finish at hf
    simpa only [finish, eval, AffineMap.lineMap_apply_one, Fin.succ_last] using hf
  constructor
  · apply (mapAtCuts_node_order hp hopen levels c 0 k 0 i 0 t (by constructor <;> norm_num)
      ⟨ht.1.le, ht.2.le⟩ hstart he).mpr
    simp only [position, Fin.val_zero, Nat.cast_zero, add_zero]
    linarith [Nat.cast_nonneg (α := ℝ) i.val, ht.1]
  · apply (mapAtCuts_node_order hp hopen levels c k (Fin.last q.segments) i (Fin.last p.bends) t 1
      ⟨ht.1.le, ht.2.le⟩ (by constructor <;> norm_num) he hfinish).mpr
    simp only [position, Fin.val_last]
    have hi : (i.val : ℝ) ≤ p.bends := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    linarith [ht.2]

end PushPuzzle.Polygonal.Route

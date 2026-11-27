/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombSpine
import all PushS.CombSpine
import all PushS.CombStations

/-! The actual bottom spine contacts only consecutive feet and the genuine tooth endpoints. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

private theorem spinePiece_atEnd (width : ℕ) (d : Graph.OrthogonalDrawing)
    (piece : Fin (d.1.length - 1)) (i : Fin (spinePiece width d piece).segments) (t : ℝ) (side : Bool) :
    (spinePiece width d piece).AtEnd i t side ↔ t = if side then 1 else 0 := by
  have hi : i.val = 0 := by have hi := i.isLt; change i.val < 1 at hi; omega
  simp only [Cslib.Polygonal.Route.AtEnd, Cslib.Polygonal.Route.position, hi, Nat.cast_zero, zero_add]
  have hseg : (spinePiece width d piece).segments = 1 := rfl
  rw [hseg, Nat.cast_one]

private theorem spine_foot_adjacent (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (vertex : Fin d.1.length)
    (i : Fin (spinePiece width d piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (spinePiece width d piece).eval i t = complexPoint (stationPoint width d (.foot vertex))) :
    vertex = spineLeft width d piece ∨ vertex = spineRight width d piece := by
  obtain ⟨rank, hv⟩ := spineVertex_surjective width d vertex
  have hb := spinePiece_column_bounds width height hd hfit piece i ht
  rw [he] at hb
  change (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) ≤
    (((prepare width d).1.getD vertex (0, 0)).1 : ℝ) ∧
    (((prepare width d).1.getD vertex (0, 0)).1 : ℝ) ≤
      (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) at hb
  rw [← hv] at hb
  have hm := spineVertex_strictMono width height hd hfit
  have hlo := hm.le_iff_le.mp (Int.cast_le.mp hb.1)
  have hhi := hm.le_iff_le.mp (Int.cast_le.mp hb.2)
  change piece.val ≤ rank.val at hlo
  change rank.val ≤ piece.val + 1 at hhi
  have hr : rank.val = piece.val ∨ rank.val = piece.val + 1 := by omega
  rcases hr with hr | hr
  · left
    exact hv.symm.trans (congrArg (spineVertex width d) (Fin.ext hr))
  · right
    exact hv.symm.trans (congrArg (spineVertex width d) (Fin.ext hr))

private theorem spinePiece_foot_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (vertex : Fin d.1.length)
    (i : Fin (spinePiece width d piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (spinePiece width d piece).eval i t = complexPoint (stationPoint width d (.foot vertex))) :
    ∃ side, (spinePiece width d piece).AtEnd i t side ∧
      (if side then spineRight width d piece else spineLeft width d piece) = vertex := by
  have hx := congrArg Complex.re he
  rw [spinePiece_eval_re] at hx
  change (1 - t) * (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) +
    t * (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) =
    (((prepare width d).1.getD vertex (0, 0)).1 : ℝ) at hx
  have hlt : (((prepare width d).1.getD (spineLeft width d piece) (0, 0)).1 : ℝ) <
      (((prepare width d).1.getD (spineRight width d piece) (0, 0)).1 : ℝ) := by
    exact_mod_cast spine_columns_strict width height hd hfit piece
  rcases spine_foot_adjacent width height hd hfit piece vertex i ht he with hv | hv
  · rw [hv] at hx
    exact ⟨false, (spinePiece_atEnd width d piece i t false).mpr (by change t = 0; nlinarith), hv.symm⟩
  · rw [hv] at hx
    exact ⟨true, (spinePiece_atEnd width d piece i t true).mpr (by change t = 1; nlinarith), hv.symm⟩

/-- A named station on a true spine piece is one of that piece's exact native feet. -/
theorem spinePiece_station_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (piece : Fin (d.1.length - 1)) (i : Fin (spinePiece width d piece).segments)
    {t : ℝ} (ht : t ∈ Set.Icc 0 1) (station : Station width d)
    (he : (spinePiece width d piece).eval i t = complexPoint (stationPoint width d station)) :
    ∃ side, (spinePiece width d piece).AtEnd i t side ∧
      Station.foot (if side then spineRight width d piece else spineLeft width d piece) = station := by
  have hy := congrArg Complex.im he
  rw [spinePiece_eval_im] at hy
  cases station with
  | tip vertex =>
    change (-2 : ℝ) = (((prepare width d).1.getD vertex (0, 0)).2 : ℝ) at hy
    have hn : (0 : ℝ) ≤ ((prepare width d).1.getD vertex (0, 0)).2 := by
      exact_mod_cast site_height_nonneg width height hfit vertex
    linarith
  | crossing hit =>
    change (-2 : ℝ) = (hit.val.height : ℝ) at hy
    have hn := (crossing_height_bounds width hd (fun r hr p hp =>
      ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩) hit.property).1
    have hn' : (0 : ℝ) ≤ hit.val.height := by exact_mod_cast hn
    linarith
  | foot vertex =>
    obtain ⟨side, hend, hv⟩ := spinePiece_foot_contact width height hd hfit piece vertex i ht he
    exact ⟨side, hend, congrArg Station.foot hv⟩

/-- Distinct ordered spine pieces meet only at their common consecutive native foot. -/
theorem spinePieces_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (left right : Fin (d.1.length - 1)) (hlr : left < right)
    (i : Fin (spinePiece width d left).segments) (j : Fin (spinePiece width d right).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (spinePiece width d left).eval i s = (spinePiece width d right).eval j t) :
    (spinePiece width d left).AtEnd i s true ∧ (spinePiece width d right).AtEnd j t false ∧
      spineRight width d left = spineLeft width d right := by
  have hm := spineVertex_strictMono width height hd hfit
  have hbc := hm.monotone (a := ⟨left.val + 1, by have := left.isLt; omega⟩)
    (b := ⟨right.val, by have := right.isLt; omega⟩) (by change left.val + 1 ≤ right.val; exact hlr)
  have hbc' : (((prepare width d).1.getD (spineRight width d left) (0, 0)).1 : ℝ) ≤
      (((prepare width d).1.getD (spineLeft width d right) (0, 0)).1 : ℝ) := by exact_mod_cast hbc
  have ha := spinePiece_column_bounds width height hd hfit left i hs
  have hb := spinePiece_column_bounds width height hd hfit right j ht
  have he' := congrArg Complex.re he
  have hla : (((prepare width d).1.getD (spineLeft width d left) (0, 0)).1 : ℝ) <
      (((prepare width d).1.getD (spineRight width d left) (0, 0)).1 : ℝ) := by
    exact_mod_cast spine_columns_strict width height hd hfit left
  have hrb : (((prepare width d).1.getD (spineLeft width d right) (0, 0)).1 : ℝ) <
      (((prepare width d).1.getD (spineRight width d right) (0, 0)).1 : ℝ) := by
    exact_mod_cast spine_columns_strict width height hd hfit right
  have hv : spineRight width d left = spineLeft width d right := by
    apply site_column_injective width height hd hfit
    exact_mod_cast (show (((prepare width d).1.getD (spineRight width d left) (0, 0)).1 : ℝ) =
      (((prepare width d).1.getD (spineLeft width d right) (0, 0)).1 : ℝ) by linarith)
  simp only [spinePiece_eval_re] at ha hb he'
  have hs1 : s = 1 := by nlinarith
  have ht0 : t = 0 := by nlinarith
  exact ⟨(spinePiece_atEnd width d left i s true).mpr hs1, (spinePiece_atEnd width d right j t false).mpr ht0, hv⟩

/-- A genuine original-edge fragment and a lower spine piece have disjoint continuous supports. -/
theorem edgeFragment_spinePiece_disjoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (edge : Fin G.edges.length)
    (hhead : (d.2.getD edge []).head? = some (Graph.drawingPosition G d G.edges[edge].1))
    (fragment : Fin ((edgeCrossings width d edge).length + 1)) (spine : Fin (d.1.length - 1)) :
    Disjoint (edgeFragment width height hd hfit edge hhead fragment).support (spinePiece width d spine).support := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  obtain ⟨i, s, hs, he⟩ := ((edgeFragment width height hd hfit edge hhead fragment).mem_support_iff z).mp hz
  obtain ⟨j, t, _, he'⟩ := ((spinePiece width d spine).mem_support_iff z).mp hw
  have hn := (edgeFragment_height_bounds width height hd hfit edge hhead fragment i hs).1
  have hy := congrArg Complex.im (he.trans he'.symm)
  rw [spinePiece_eval_im] at hy
  linarith

/-- A tooth and spine piece meet only at their common actual named foot. -/
theorem toothPiece_spinePiece_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (tooth : Fin ((toothCrossings width d vertex).length + 1)) (spine : Fin (d.1.length - 1))
    (i : Fin (toothPiece width d vertex tooth).segments) (j : Fin (spinePiece width d spine).segments)
    {s t : ℝ} (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (toothPiece width d vertex tooth).eval i s = (spinePiece width d spine).eval j t) :
    ∃ a b, (toothPiece width d vertex tooth).AtEnd i s a ∧ (spinePiece width d spine).AtEnd j t b ∧
      toothStation width d vertex (if a then tooth.succ else tooth.castSucc) =
        .foot (if b then spineRight width d spine else spineLeft width d spine) := by
  have hp : (toothPiece width d vertex tooth).eval i s = complexPoint (stationPoint width d (.foot vertex)) := by
    apply Complex.ext
    · exact toothPiece_eval_re width d vertex tooth i s
    · rw [he, spinePiece_eval_im]
      change (-2 : ℝ) = ((-2 : ℤ) : ℝ)
      norm_num
  obtain ⟨a, ha, hname⟩ := toothPiece_station_contact width height hd hfit vertex tooth i hs (.foot vertex) hp
  obtain ⟨b, hb, hname'⟩ := spinePiece_station_contact width height hd hfit spine j ht (.foot vertex) (he.symm.trans hp)
  exact ⟨a, b, ha, hb, hname.trans hname'.symm⟩

end PushPuzzle.PushS.Comb

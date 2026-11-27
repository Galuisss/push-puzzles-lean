/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombStations
public import CslibFrontier.Foundations.Geometry.Polygonal.Segment
public import CslibFrontier.Foundations.Geometry.Orthogonal.Polygonal
import all PushS.CombPartition
import all PushS.CombStations

/-! Each actual comb tooth is split at precisely its strictly ordered genuine source encounters. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib

open Cslib.Complexity

open Cslib.Orthogonal

/-- The complete bottom-to-top station sequence of one actual source tooth. -/
@[expose] def toothStations (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    List (Station width d) :=
  .foot vertex :: (toothCrossings width d vertex).attach.map (fun hit =>
    .crossing ⟨hit.val, by exact (tooth_mem width d hit.property).1⟩) ++ [.tip vertex]

/-- Every actual crossing contributes precisely one internal station to its tooth. -/
theorem toothStations_length (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length) :
    (toothStations width d vertex).length = (toothCrossings width d vertex).length + 2 := by
  simp only [toothStations, List.length_cons, List.length_append, List.length_map,
    List.length_attach, List.length_nil]

private theorem toothStation_cases (width : ℕ) (d : Graph.OrthogonalDrawing)
    (vertex : Fin d.1.length) {station : Station width d} (hs : station ∈ toothStations width d vertex) :
    station = .foot vertex ∨ station = .tip vertex ∨
      ∃ hit : {c // c ∈ crossings width d}, hit.val ∈ toothCrossings width d vertex ∧ station = .crossing hit := by
  rcases List.mem_cons.mp hs with hs | hs
  · exact Or.inl hs
  · rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨hit, _, rfl⟩ := List.mem_map.mp hs
      exact Or.inr (Or.inr ⟨_, hit.property, rfl⟩)
    · exact Or.inr (Or.inl (List.mem_singleton.mp hs))

/-- All actual stations on one tooth have exactly its original prepared physical column. -/
theorem toothStations_column (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    {station : Station width d} (hs : station ∈ toothStations width d vertex) :
    (stationPoint width d station).1 = ((prepare width d).1.getD vertex (0, 0)).1 := by
  rcases toothStation_cases width d vertex hs with rfl | rfl | ⟨hit, hc, rfl⟩
  · rfl
  · rfl
  · change ((prepare width d).1.getD hit.val.vertex (0, 0)).1 = _
    rw [(tooth_mem width d hc).2]

private theorem crossing_below_tip (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    {c : Crossing} (hc : c ∈ toothCrossings width d vertex) :
    c.height < ((prepare width d).1.getD vertex (0, 0)).2 := by
  obtain ⟨hm, hv⟩ := tooth_mem width d hc
  obtain ⟨_, _, site, _, _, hs, ht, hh, _⟩ := (mem_crossings_iff width d c).mp hm
  have hsite : (prepare width d).1.getD vertex (0, 0) = site := by
    simp only [hv] at hs
    simp only [List.getD_eq_getElem?_getD, hs, Option.getD_some]
  rw [hsite, hh]
  exact ht.2

/-- The complete tooth station array follows strictly increasing actual integer height. -/
theorem toothStations_strict (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) :
    (toothStations width d vertex).Pairwise
      (fun a b => (stationPoint width d a).2 < (stationPoint width d b).2) := by
  let hits := toothCrossings width d vertex
  have hp := toothCrossings_strict width hd (fun p hp => ⟨(hfit.1 p hp).1, (hfit.1 p hp).2.1⟩)
    (fun r hr p hp => ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩) vertex
  have hattach : hits.attach.map Subtype.val = hits := by simp
  dsimp only [hits] at hattach
  rw [← hattach, List.pairwise_map] at hp
  have hc (hit : {c // c ∈ hits}) : 0 ≤ hit.val.height :=
    (crossing_height_bounds width hd (fun r hr p hp =>
      ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩) (tooth_mem width d hit.property).1).1
  apply List.pairwise_cons.mpr
  constructor
  · intro station hs
    rcases List.mem_append.mp hs with hs | hs
    · obtain ⟨hit, _, rfl⟩ := List.mem_map.mp hs
      change (-2 : ℤ) < hit.val.height
      have := hc hit
      omega
    · have he := List.mem_singleton.mp hs
      subst station
      change (-2 : ℤ) < ((prepare width d).1.getD vertex (0, 0)).2
      have := site_height_nonneg width height hfit vertex
      omega
  · apply List.pairwise_append.mpr
    refine ⟨?_, by simp, ?_⟩
    · rw [List.pairwise_map]
      exact hp
    · intro station hs tip ht
      obtain ⟨hit, _, rfl⟩ := List.mem_map.mp hs
      have he := List.mem_singleton.mp ht
      subst tip
      exact crossing_below_tip width d vertex hit.property

/-- Select one literal actual tooth station by its position in that tooth's array. -/
@[expose] def toothStation (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (index : Fin ((toothCrossings width d vertex).length + 2)) : Station width d :=
  (toothStations width d vertex).get ⟨index.val, by rw [toothStations_length]; exact index.isLt⟩

/-- The selected tooth heights form a strictly increasing finite map. -/
theorem toothStation_strictMono (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) :
    StrictMono (fun index => (stationPoint width d (toothStation width d vertex index)).2) := by
  intro i j hij
  exact List.pairwise_iff_get.mp (toothStations_strict width height hd hfit vertex) _ _ hij

private theorem toothStation_mem (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (index : Fin ((toothCrossings width d vertex).length + 2)) :
    toothStation width d vertex index ∈ toothStations width d vertex :=
  List.get_mem _ _

/-- All indexed tooth stations retain that tooth's exact native prepared column. -/
theorem toothStation_column (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (index : Fin ((toothCrossings width d vertex).length + 2)) :
    (stationPoint width d (toothStation width d vertex index)).1 =
      ((prepare width d).1.getD vertex (0, 0)).1 :=
  toothStations_column width d vertex (toothStation_mem width d vertex index)

/-- One genuine straight tooth piece between consecutive actual source stations. -/
@[expose] noncomputable def toothPiece (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) : Cslib.Polygonal.Route :=
  Cslib.Polygonal.Route.line
    (complexPoint (stationPoint width d (toothStation width d vertex piece.castSucc)))
    (complexPoint (stationPoint width d (toothStation width d vertex piece.succ)))

/-- Each actual tooth piece has precisely its two original numbered boundary stations. -/
theorem toothPiece_endpoint (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1)) (side : Bool) :
    (toothPiece width d vertex piece).endpoint side =
      complexPoint (stationPoint width d (toothStation width d vertex (if side then piece.succ else piece.castSucc))) := by
  cases side <;> rfl

/-- Every actual straight tooth piece is a nondegenerate simple polygonal route. -/
theorem toothPiece_simple (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) (piece : Fin ((toothCrossings width d vertex).length + 1)) :
    (toothPiece width d vertex piece).IsSimple := by
  apply Cslib.Polygonal.Route.isSimple_line
  intro he
  have hy := congrArg Complex.im he
  change ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) =
    ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) at hy
  have hstrict := toothStation_strictMono width height hd hfit vertex (a := piece.castSucc)
    (b := piece.succ) Fin.castSucc_lt_succ
  exact (ne_of_lt hstrict) (Int.cast_inj.mp hy)

/-- Every real parameter of an actual tooth piece stays on that tooth's exact column. -/
theorem toothPiece_eval_re (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) (t : ℝ) :
    ((toothPiece width d vertex piece).eval i t).re =
      (((prepare width d).1.getD vertex (0, 0)).1 : ℝ) := by
  have heval : (toothPiece width d vertex piece).eval i t = AffineMap.lineMap
      (complexPoint (stationPoint width d (toothStation width d vertex piece.castSucc)))
      (complexPoint (stationPoint width d (toothStation width d vertex piece.succ))) t :=
    Cslib.Polygonal.Route.eval_line _ _ i t
  rw [heval]
  simp only [AffineMap.lineMap_apply_module, Complex.add_re, Complex.smul_re]
  change (1 - t) * ((stationPoint width d (toothStation width d vertex piece.castSucc)).1 : ℝ) +
    t * ((stationPoint width d (toothStation width d vertex piece.succ)).1 : ℝ) = _
  rw [toothStation_column, toothStation_column]
  ring

private theorem toothPiece_eval_im (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) (t : ℝ) :
    ((toothPiece width d vertex piece).eval i t).im =
      (1 - t) * ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) +
        t * ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) := by
  have heval : (toothPiece width d vertex piece).eval i t = AffineMap.lineMap
      (complexPoint (stationPoint width d (toothStation width d vertex piece.castSucc)))
      (complexPoint (stationPoint width d (toothStation width d vertex piece.succ))) t :=
    Cslib.Polygonal.Route.eval_line _ _ i t
  rw [heval]
  simp only [AffineMap.lineMap_apply_module, Complex.add_im, Complex.smul_im]
  rfl

/-- Every real point on an actual tooth piece lies between its two exact boundary heights. -/
theorem toothPiece_height_bounds (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1) :
    ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) ≤
      ((toothPiece width d vertex piece).eval i t).im ∧
      ((toothPiece width d vertex piece).eval i t).im ≤
        ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) := by
  have hlt := toothStation_strictMono width height hd hfit vertex
    (a := piece.castSucc) (b := piece.succ) Fin.castSucc_lt_succ
  have hle : ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) ≤
      ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) := by exact_mod_cast hlt.le
  rw [toothPiece_eval_im]
  constructor <;> nlinarith [mul_nonneg ht.1 (sub_nonneg.mpr hle),
    mul_nonneg (sub_nonneg.mpr ht.2) (sub_nonneg.mpr hle)]

private theorem toothPiece_atEnd (width : ℕ) (d : Graph.OrthogonalDrawing) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) (t : ℝ) (side : Bool) :
    (toothPiece width d vertex piece).AtEnd i t side ↔ t = if side then 1 else 0 := by
  have hi : i.val = 0 := by
    have hi := i.isLt
    change i.val < 1 at hi
    omega
  simp only [Cslib.Polygonal.Route.AtEnd, Cslib.Polygonal.Route.position, hi, Nat.cast_zero, zero_add]
  have hseg : (toothPiece width d vertex piece).segments = 1 := rfl
  rw [hseg, Nat.cast_one]

/-- Distinct ordered pieces of one actual tooth contact only at their shared boundary station. -/
theorem toothPieces_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (vertex : Fin d.1.length) (left right : Fin ((toothCrossings width d vertex).length + 1))
    (hlr : left < right) (i : Fin (toothPiece width d vertex left).segments)
    (j : Fin (toothPiece width d vertex right).segments) (s t : ℝ)
    (hs : s ∈ Set.Icc 0 1) (ht : t ∈ Set.Icc 0 1)
    (he : (toothPiece width d vertex left).eval i s = (toothPiece width d vertex right).eval j t) :
    left.val + 1 = right.val ∧ (toothPiece width d vertex left).AtEnd i s true ∧
      (toothPiece width d vertex right).AtEnd j t false := by
  have hm := toothStation_strictMono width height hd hfit vertex
  have hbc := hm.monotone (a := left.succ) (b := right.castSucc) (by exact hlr)
  have hbc' : ((stationPoint width d (toothStation width d vertex left.succ)).2 : ℝ) ≤
      ((stationPoint width d (toothStation width d vertex right.castSucc)).2 : ℝ) := by exact_mod_cast hbc
  have ha := toothPiece_height_bounds width height hd hfit vertex left i hs
  have hb := toothPiece_height_bounds width height hd hfit vertex right j ht
  have he' := congrArg Complex.im he
  have hsame : (stationPoint width d (toothStation width d vertex left.succ)).2 =
      (stationPoint width d (toothStation width d vertex right.castSucc)).2 := by
    exact_mod_cast (show ((stationPoint width d (toothStation width d vertex left.succ)).2 : ℝ) =
      ((stationPoint width d (toothStation width d vertex right.castSucc)).2 : ℝ) by linarith)
  have hindex := congrArg Fin.val (hm.injective hsame)
  have hla := hm (a := left.castSucc) (b := left.succ) Fin.castSucc_lt_succ
  have hrb := hm (a := right.castSucc) (b := right.succ) Fin.castSucc_lt_succ
  have hla' : ((stationPoint width d (toothStation width d vertex left.castSucc)).2 : ℝ) <
      ((stationPoint width d (toothStation width d vertex left.succ)).2 : ℝ) := by exact_mod_cast hla
  have hrb' : ((stationPoint width d (toothStation width d vertex right.castSucc)).2 : ℝ) <
      ((stationPoint width d (toothStation width d vertex right.succ)).2 : ℝ) := by exact_mod_cast hrb
  simp only [toothPiece_eval_im] at ha hb he'
  have hs1 : s = 1 := by nlinarith
  have ht0 : t = 0 := by nlinarith
  exact ⟨hindex, (toothPiece_atEnd width d vertex left i s true).mpr hs1,
    (toothPiece_atEnd width d vertex right j t false).mpr ht0⟩

/-- Pieces on two different native teeth have disjoint continuous supports. -/
theorem toothPieces_disjoint (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    (left right : Fin d.1.length) (hlr : left ≠ right)
    (a : Fin ((toothCrossings width d left).length + 1))
    (b : Fin ((toothCrossings width d right).length + 1)) :
    Disjoint (toothPiece width d left a).support (toothPiece width d right b).support := by
  apply Set.disjoint_left.mpr
  intro z hz hw
  obtain ⟨i, s, _, hs⟩ := ((toothPiece width d left a).mem_support_iff z).mp hz
  obtain ⟨j, t, _, ht⟩ := ((toothPiece width d right b).mem_support_iff z).mp hw
  have he := congrArg Complex.re (hs.trans ht.symm)
  rw [toothPiece_eval_re, toothPiece_eval_re] at he
  exact hlr (site_column_injective width height hd hfit (Int.cast_inj.mp he))

end PushPuzzle.PushS.Comb

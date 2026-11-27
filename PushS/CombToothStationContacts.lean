/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombTeeth
import all PushS.CombTeeth
import all PushS.CombStations

/-! Every actual named station on a tooth piece is one of its own two named ends. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- The original source tooth to which an actual station belongs. -/
@[expose] def Station.tooth {width : ℕ} {d : Graph.OrthogonalDrawing} : Station width d → Fin d.1.length
  | .tip vertex => vertex
  | .crossing hit => ⟨hit.val.vertex, by exact crossing_vertex_lt width d hit.property⟩
  | .foot vertex => vertex

/-- Every actual station retains its own source tooth's exact physical column. -/
theorem stationPoint_column (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) :
    (stationPoint width d station).1 = ((prepare width d).1.getD station.tooth (0, 0)).1 := by
  cases station <;> rfl

/-- Every actual station occurs in its own source tooth's literal station array. -/
theorem station_mem_toothStations (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) :
    station ∈ toothStations width d station.tooth := by
  cases station with
  | tip vertex => simp [toothStations, Station.tooth]
  | foot vertex => simp [toothStations, Station.tooth]
  | crossing hit =>
    apply List.mem_append_left
    apply List.mem_cons_of_mem
    apply List.mem_map.mpr
    have hc : hit.val ∈ toothCrossings width d hit.val.vertex :=
      (toothCrossings_perm width d hit.val.vertex).mem_iff.mpr (List.mem_filter.mpr ⟨hit.property, by simp⟩)
    exact ⟨⟨hit.val, hc⟩, List.mem_attach _ _, rfl⟩

private theorem tooth_cut_adjacent (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (cut : Fin ((toothCrossings width d vertex).length + 2))
    (i : Fin (toothPiece width d vertex piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (toothPiece width d vertex piece).eval i t =
      complexPoint (stationPoint width d (toothStation width d vertex cut))) :
    cut = piece.castSucc ∨ cut = piece.succ := by
  have hm := toothStation_strictMono width height hd hfit vertex
  have hb := toothPiece_height_bounds width height hd hfit vertex piece i ht
  rw [he] at hb
  change ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) ≤
      ((stationPoint width d (toothStation width d vertex cut)).2 : ℝ) ∧
      ((stationPoint width d (toothStation width d vertex cut)).2 : ℝ) ≤
        ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) at hb
  have hlo := hm.le_iff_le.mp (Int.cast_le.mp hb.1)
  have hhi := hm.le_iff_le.mp (Int.cast_le.mp hb.2)
  apply or_iff_not_imp_left.mpr
  intro hne
  apply Fin.ext
  have hne' : cut.val ≠ piece.val := fun h => hne (Fin.ext h)
  change piece.val ≤ cut.val at hlo
  change cut.val ≤ piece.val + 1 at hhi
  change cut.val = piece.val + 1
  omega

/-- A genuine tooth piece meets a station on its own tooth only at its exact named boundary. -/
theorem toothPiece_cut_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (cut : Fin ((toothCrossings width d vertex).length + 2))
    (i : Fin (toothPiece width d vertex piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (he : (toothPiece width d vertex piece).eval i t =
      complexPoint (stationPoint width d (toothStation width d vertex cut))) :
    ∃ side, (toothPiece width d vertex piece).AtEnd i t side ∧ cut = if side then piece.succ else piece.castSucc := by
  have hy := congrArg Complex.im he
  rw [toothPiece_eval_im] at hy
  change (1 - t) * ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) +
    t * ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) =
    ((stationPoint width d (toothStation width d vertex cut)).2 : ℝ) at hy
  have hlt := toothStation_strictMono width height hd hfit vertex
    (a := piece.castSucc) (b := piece.succ) Fin.castSucc_lt_succ
  have hlt' : ((stationPoint width d (toothStation width d vertex piece.castSucc)).2 : ℝ) <
      ((stationPoint width d (toothStation width d vertex piece.succ)).2 : ℝ) := by exact_mod_cast hlt
  rcases tooth_cut_adjacent width height hd hfit vertex piece cut i ht he with rfl | rfl
  · exact ⟨false, (toothPiece_atEnd width d vertex piece i t false).mpr (by change t = 0; nlinarith), rfl⟩
  · exact ⟨true, (toothPiece_atEnd width d vertex piece i t true).mpr (by change t = 1; nlinarith), rfl⟩

/-- Every named comb station on an actual tooth piece is exactly one of its own named ends. -/
theorem toothPiece_station_contact (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) (vertex : Fin d.1.length)
    (piece : Fin ((toothCrossings width d vertex).length + 1))
    (i : Fin (toothPiece width d vertex piece).segments) {t : ℝ} (ht : t ∈ Set.Icc 0 1)
    (station : Station width d)
    (he : (toothPiece width d vertex piece).eval i t = complexPoint (stationPoint width d station)) :
    ∃ side, (toothPiece width d vertex piece).AtEnd i t side ∧
      toothStation width d vertex (if side then piece.succ else piece.castSucc) = station := by
  have hx := congrArg Complex.re he
  rw [toothPiece_eval_re] at hx
  change (((prepare width d).1.getD vertex (0, 0)).1 : ℝ) = ((stationPoint width d station).1 : ℝ) at hx
  rw [stationPoint_column] at hx
  have hv := site_column_injective width height hd hfit (Int.cast_inj.mp hx)
  have hc := station_mem_toothStations width d station
  rw [← hv] at hc
  obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
  let cut : Fin ((toothCrossings width d vertex).length + 2) := ⟨k.val, by
    rw [← toothStations_length width d vertex]
    exact k.isLt⟩
  have hcut : toothStation width d vertex cut = station := hk
  have he' : (toothPiece width d vertex piece).eval i t =
      complexPoint (stationPoint width d (toothStation width d vertex cut)) := by rw [hcut]; exact he
  obtain ⟨side, hend, hs⟩ := toothPiece_cut_contact width height hd hfit vertex piece cut i ht he'
  exact ⟨side, hend, hs ▸ hcut⟩

end PushPuzzle.PushS.Comb

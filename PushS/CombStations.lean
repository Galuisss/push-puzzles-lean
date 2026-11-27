/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.CombToothContacts
import all PushS.CombToothOrder
import all PushS.CombCrossingGeometry

/-! The actual original tips, crossing stations and lower comb feet have distinct positions. -/

public section
namespace PushPuzzle.PushS.Comb

open Cslib.Complexity

open Cslib.Orthogonal

/-- An actual source tip, a genuine emitted crossing, or the foot of that source tooth. -/
inductive Station (width : ℕ) (d : Graph.OrthogonalDrawing) where
  | tip (vertex : Fin d.1.length)
  | crossing (hit : {c // c ∈ crossings width d})
  | foot (vertex : Fin d.1.length)
  deriving DecidableEq

/-- The literal prepared integer location of an actual comb station. -/
@[expose] def stationPoint (width : ℕ) (d : Graph.OrthogonalDrawing) : Station width d → Point
  | .tip v => (prepare width d).1.getD v (0, 0)
  | .crossing c => c.val.location width d
  | .foot v => (((prepare width d).1.getD v (0, 0)).1, -2)

/-- The complete indexed station array of the actual source comb. -/
@[expose] def stations (width : ℕ) (d : Graph.OrthogonalDrawing) : List (Station width d) :=
  List.ofFn Station.tip ++ (crossings width d).attach.map Station.crossing ++ List.ofFn Station.foot

/-- Every source tip, actual crossing and comb foot occurs in its literal station array. -/
theorem stations_complete (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) :
    station ∈ stations width d := by
  cases station <;> simp [stations]

/-- The actual station array has no repeated indexed station. -/
theorem stations_nodup (width : ℕ) (d : Graph.OrthogonalDrawing) : (stations width d).Nodup := by
  have htip : (List.ofFn (Station.tip (width := width) (d := d))).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => Station.tip.inj h)
  have hfoot : (List.ofFn (Station.foot (width := width) (d := d))).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ h => Station.foot.inj h)
  have hcross : ((crossings width d).attach.map Station.crossing).Nodup := by
    apply List.Nodup.map (fun _ _ h => Station.crossing.inj h)
    simpa only [List.nodup_attach] using crossings_nodup width d
  have htc : List.Disjoint (List.ofFn (Station.tip (width := width) (d := d)))
      ((crossings width d).attach.map Station.crossing) := by simp [List.disjoint_left]
  have htf : List.Disjoint (List.ofFn (Station.tip (width := width) (d := d)))
      (List.ofFn Station.foot) := by simp [List.disjoint_left]
  have hcf : List.Disjoint ((crossings width d).attach.map Station.crossing)
      (List.ofFn (Station.foot (width := width) (d := d))) := by
    apply List.disjoint_left.mpr
    intro station hc hf
    obtain ⟨c, _, rfl⟩ := List.mem_map.mp hc
    obtain ⟨v, he⟩ := List.mem_ofFn.mp hf
    cases he
  exact (htip.append hcross htc).append hfoot (List.disjoint_append_left.mpr ⟨htf, hcf⟩)

/-- The station array retains exactly the two ends of each tooth and every actual crossing. -/
theorem stations_length (width : ℕ) (d : Graph.OrthogonalDrawing) :
    (stations width d).length = 2 * d.1.length + (crossings width d).length := by
  simp only [stations, List.length_append, List.length_ofFn, List.length_map, List.length_attach]
  omega

/-- The literal position of one station in its actual complete source-comb array. -/
@[expose] def stationNumber (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) : ℕ :=
  (stations width d).idxOf station

/-- The actual integer coordinates of the complete station array, in that same order. -/
@[expose] def stationPositions (width : ℕ) (d : Graph.OrthogonalDrawing) : List Point :=
  (stations width d).map (stationPoint width d)

/-- The coordinate of a station label in the existing listed-graph representation. -/
@[expose] def stationPosition (width : ℕ) (d : Graph.OrthogonalDrawing) (label : ℕ) : Point :=
  (stationPositions width d).getD label (0, 0)

/-- Every actual station has an in-bounds stored label. -/
theorem stationNumber_lt (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) :
    stationNumber width d station < (stations width d).length :=
  List.idxOf_lt_length_of_mem (stations_complete width d station)

/-- Numbered source-comb labels retain every actual station identity. -/
theorem stationNumber_injective (width : ℕ) (d : Graph.OrthogonalDrawing) :
    Function.Injective (stationNumber width d) := by
  intro a b he
  exact (List.idxOf_inj (stations_complete width d a)).mp he

/-- Reading an actual station label returns exactly its original prepared coordinate. -/
theorem stationPosition_number (width : ℕ) (d : Graph.OrthogonalDrawing) (station : Station width d) :
    stationPosition width d (stationNumber width d station) = stationPoint width d station := by
  have hi : stationNumber width d station < (stationPositions width d).length := by
    simpa only [stationPositions, List.length_map] using stationNumber_lt width d station
  rw [stationPosition, List.getD_eq_getElem _ _ hi]
  simp only [stationPositions, List.getElem_map, stationNumber, List.getElem_idxOf]

private theorem site_height_nonneg (width height : ℕ) {d : Graph.OrthogonalDrawing}
    (hfit : Graph.drawingFits d width height) (v : Fin d.1.length) :
    0 ≤ ((prepare width d).1.getD v (0, 0)).2 := by
  have hm : d.1.getD v (0, 0) ∈ d.1 := by
    rw [List.getD_eq_getElem _ _ v.isLt]
    exact List.getElem_mem v.isLt
  have hx := (hfit.1 _ hm).1
  rw [site_prepare]
  change 0 ≤ 2 * (d.1.getD v (0, 0)).1
  omega

private theorem site_column_injective (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    {a b : Fin d.1.length}
    (he : ((prepare width d).1.getD a (0, 0)).1 = ((prepare width d).1.getD b (0, 0)).1) : a = b := by
  have hn := prepared_columns_nodup width height hd hfit
  have hi (v : Fin d.1.length) : v.val < ((prepare width d).1.map Prod.fst).length := by
    simpa only [List.length_map, prepare] using v.isLt
  have hm (v : Fin d.1.length) : ((prepare width d).1.map Prod.fst).getD v 0 =
      ((prepare width d).1.getD v (0, 0)).1 :=
    List.getD_map (l := (prepare width d).1) (d := (0, 0)) (n := v.val) Prod.fst
  apply Fin.ext
  exact (hn.getD_inj (hi a) (hi b)).mp (by rw [hm, hm]; exact he)

private theorem crossing_ne_site (width height : ℕ) {d : Graph.OrthogonalDrawing}
    (hfit : Graph.drawingFits d width height)
    (hit : {c // c ∈ crossings width d}) (vertex : Fin d.1.length) :
    hit.val.location width d ≠ (prepare width d).1.getD vertex (0, 0) := by
  have hm : d.1.getD vertex (0, 0) ∈ d.1 := by
    rw [List.getD_eq_getElem _ _ vertex.isLt]
    exact List.getElem_mem vertex.isLt
  have hbound := hfit.1 _ hm
  rw [site_prepare]
  exact crossing_location_ne_point width d (fun p hp => ⟨(hfit.1 p hp).1, (hfit.1 p hp).2.1⟩)
    hit.property _ ⟨hbound.1, hbound.2.1⟩

/-- Every actual tip, crossing and comb foot has its own physical point in the supplied strip. -/
theorem stationPoint_injective (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    Function.Injective (stationPoint width d) := by
  have hc (hit : {c // c ∈ crossings width d}) : 0 ≤ hit.val.height :=
    (crossing_height_bounds width hd (fun r hr p hp => ⟨(hfit.2 r hr p hp).1, (hfit.2 r hr p hp).2.1⟩) hit.property).1
  intro a b he
  cases a with
  | tip v =>
    cases b with
    | tip w => exact congrArg Station.tip (site_column_injective width height hd hfit (congrArg Prod.fst he))
    | crossing c => exact False.elim (crossing_ne_site width height hfit c v he.symm)
    | foot w =>
      have hy := congrArg Prod.snd he
      have hn := site_height_nonneg width height hfit v
      change ((prepare width d).1.getD v (0, 0)).2 = -2 at hy
      omega
  | crossing c =>
    cases b with
    | tip v => exact False.elim (crossing_ne_site width height hfit c v he)
    | crossing c' =>
      have hh : c.val = c'.val := crossing_location_injective width hd
        (fun p hp => ⟨(hfit.1 p hp).1, (hfit.1 p hp).2.1⟩) c.property c'.property he
      exact congrArg Station.crossing (Subtype.ext hh)
    | foot v =>
      have hy := congrArg Prod.snd he
      change c.val.height = -2 at hy
      have hn := hc c
      omega
  | foot v =>
    cases b with
    | tip w =>
      have hy := congrArg Prod.snd he
      have hn := site_height_nonneg width height hfit w
      change (-2 : ℤ) = ((prepare width d).1.getD w (0, 0)).2 at hy
      omega
    | crossing c =>
      have hy := congrArg Prod.snd he
      change (-2 : ℤ) = c.val.height at hy
      have hn := hc c
      omega
    | foot w =>
      have hx := congrArg Prod.fst he
      change ((prepare width d).1.getD v (0, 0)).1 = ((prepare width d).1.getD w (0, 0)).1 at hx
      exact congrArg Station.foot (site_column_injective width height hd hfit hx)

/-- The same actual source-comb coordinate array has no repeated physical point. -/
theorem stationPositions_nodup (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height) :
    (stationPositions width d).Nodup :=
  (stations_nodup width d).map (stationPoint_injective width height hd hfit)

/-- Actual declared station labels with equal coordinates are the same listed graph vertex. -/
theorem stationPosition_injective (width height : ℕ) {G : Graph} {d : Graph.OrthogonalDrawing}
    (hd : G.IsPlanarOrthogonalDrawing d) (hfit : Graph.drawingFits d width height)
    {a b : ℕ} (ha : a < (stationPositions width d).length) (hb : b < (stationPositions width d).length)
    (he : stationPosition width d a = stationPosition width d b) : a = b :=
  ((stationPositions_nodup width height hd hfit).getD_inj ha hb).mp he

end PushPuzzle.PushS.Comb

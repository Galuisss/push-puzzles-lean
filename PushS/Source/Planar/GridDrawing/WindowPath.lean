/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Planar.GridDrawing.WindowRoute
import all PushS.Source.Planar.GridDrawing.WindowRoute
import Mathlib.Data.List.Basic

/-!
# Actual grid paths of the selected fixed-window routes

The selected route moves only downward. Each unit edge is one horizontal or downward vertical
segment, so their concatenation is an actual `GridRouting.Path`. Its normalized unit route is
exactly the selected original point list.

## Main results

* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_unitRoute`: exact selected normalized point list.
* `PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath_points`: all path lattice points were marked.
-/

public section

namespace PushPuzzle.NCL.GridDrawing.WindowRoute

open Cslib.Complexity Cslib.Complexity.NCL Cslib.Complexity.NCL.GridDrawing Cslib

/-- Retain the original nonnegative coordinates of the finite window point. -/
@[expose] def gridPoint {width span : ℕ} (p : Point width span) : GridRouting.Point :=
  (p.1.val, p.2.val)

private def edgePath {width span : ℕ} (p q : Point width span) (h : step p q = true) :
    GridRouting.Path (gridPoint p) (gridPoint q) :=
  let hp : (graph width span).Adj p q ∧ p.2.val ≤ q.2.val := of_decide_eq_true h
  if hx : p.1.val = q.1.val then
    (GridRouting.Path.vertical p.1.val p.2.val q.2.val hp.2).cast rfl (Prod.ext hx rfl)
  else
    let hy : p.2.val = q.2.val := by
      have hu := hp.1
      change Nat.dist p.1.val q.1.val + Nat.dist p.2.val q.2.val = 1 at hu
      simp only [Nat.dist] at hu
      omega
    (GridRouting.Path.horizontal p.1.val q.1.val p.2.val).cast rfl (Prod.ext rfl hy)

private theorem support_unitWalk_cast {p q p' q' : GridRouting.Point}
    (P : GridRouting.Path p q) (hp : p = p') (hq : q = q') :
    (PushPuzzle.NCL.GridRouting.Path.unitWalk (P.cast hp hq)).support = (PushPuzzle.NCL.GridRouting.Path.unitWalk P).support := by
  cases hp
  cases hq
  rfl

private theorem segmentWalk_one {a b : Orthogonal.Point}
    (ha : a.1 = b.1 ∨ a.2 = b.2) (hu : Orthogonal.length a b = 1) :
    Orthogonal.segmentWalk a b = [a, b] := by
  have hn : (Orthogonal.segmentWalk a b).length = 2 := by
    rw [Orthogonal.segmentWalk_length, hu]
  obtain ⟨u, v, hr⟩ := List.length_eq_two.mp hn
  have hs := Orthogonal.segmentWalk_head a b
  have ht := Orthogonal.segmentWalk_last ha
  rw [hr] at hs ht
  have hs' : u = a := Option.some.inj hs
  have ht' : v = b := Option.some.inj ht
  simpa only [hs', ht'] using hr

private theorem support_edgePath {width span : ℕ} (p q : Point width span)
    (h : step p q = true) : (PushPuzzle.NCL.GridRouting.Path.unitWalk (edgePath p q h)).support = [point p, point q] := by
  have hp : (graph width span).Adj p q ∧ p.2.val ≤ q.2.val := of_decide_eq_true h
  have hu : Orthogonal.length (point p) (point q) = 1 := (gridHom width span).map_rel hp.1
  dsimp only [edgePath]
  split
  · rename_i hx
    erw [support_unitWalk_cast, GridRouting.Path.unitWalk, GridDrawing.support_segmentUnitWalk]
    have he : GridDrawing.integerPoint (p.1.val, q.2.val) = point q := by
      simp only [GridDrawing.integerPoint, point, hx]
    rw [he]
    exact segmentWalk_one (Or.inl (congrArg Int.ofNat hx)) hu
  · rename_i hx
    erw [support_unitWalk_cast, GridRouting.Path.unitWalk, GridDrawing.support_segmentUnitWalk]
    have hy : p.2.val = q.2.val := by
      have hh := hp.1
      simp only [graph, Nat.dist] at hh
      omega
    have he : GridDrawing.integerPoint (q.1.val, p.2.val) = point q := by
      simp only [GridDrawing.integerPoint, point, hy]
    rw [he]
    exact segmentWalk_one (Or.inr (congrArg Int.ofNat hy)) hu

private theorem contains_edgePath {width span : ℕ} (p q : Point width span)
    (h : step p q = true) (x : GridRouting.Point) :
    (edgePath p q h).Contains x ↔ gridPoint p = x ∨ gridPoint q = x := by
  have hp : (graph width span).Adj p q ∧ p.2.val ≤ q.2.val := of_decide_eq_true h
  have hu := hp.1
  simp only [graph, Nat.dist] at hu
  dsimp only [edgePath]
  split <;> erw [GridRouting.Path.contains_cast_iff] <;>
    simp only [GridRouting.Path.Contains, gridPoint, Prod.ext_iff] <;> omega

private def listPath {width span : ℕ} : (r : List (Point width span)) →
    (hne : r ≠ []) → r.IsChain (fun p q => step p q = true) →
      GridRouting.Path (gridPoint (r.head hne)) (gridPoint (r.getLast hne))
  | [], hne, _ => (hne rfl).elim
  | [p], _, _ => .horizontal p.1.val p.1.val p.2.val
  | p :: q :: r, _, hc => (edgePath p q hc.rel).comp
      (listPath (q :: r) (List.cons_ne_nil _ _) hc.tail)

private theorem support_listPath {width span : ℕ} (r : List (Point width span))
    (hne : r ≠ []) (hc : r.IsChain (fun p q => step p q = true)) :
    (PushPuzzle.NCL.GridRouting.Path.unitWalk (listPath r hne hc)).support = r.map point := by
  induction r with
  | nil => exact False.elim (hne rfl)
  | cons p r ih =>
    cases r with
    | nil =>
      dsimp only [listPath, GridRouting.Path.unitWalk]
      erw [GridDrawing.support_segmentUnitWalk]
      simp [Orthogonal.segmentWalk, Orthogonal.walk, Orthogonal.length,
        GridDrawing.integerPoint, gridPoint, point]
    | cons q r =>
      dsimp only [listPath]
      erw [GridRouting.Path.unitWalk.eq_def,
        SimpleGraph.Walk.support_append_eq_support_dropLast_append,
        support_edgePath, ih (List.cons_ne_nil _ _) hc.tail]
      rfl

private theorem contains_listPath {width span : ℕ} (r : List (Point width span))
    (hne : r ≠ []) (hc : r.IsChain (fun p q => step p q = true)) (x : GridRouting.Point) :
    (listPath r hne hc).Contains x ↔ ∃ p ∈ r, gridPoint p = x := by
  induction r with
  | nil => exact False.elim (hne rfl)
  | cons p r ih =>
    cases r with
    | nil =>
      change (GridRouting.Path.horizontal p.1.val p.1.val p.2.val).Contains x ↔ _
      simp only [List.mem_singleton, exists_eq_left]
      simp only [GridRouting.Path.Contains, Nat.min_self, Nat.max_self, gridPoint, Prod.ext_iff]
      omega
    | cons q r =>
      dsimp only [listPath]
      erw [GridRouting.Path.Contains, contains_edgePath, ih (List.cons_ne_nil _ _) hc.tail]
      simp only [List.mem_cons, exists_eq_or_imp]
      tauto

private theorem unitRoute_cast {p q p' q' : GridRouting.Point}
    (P : GridRouting.Path p q) (hp : p = p') (hq : q = q') :
    (P.cast hp hq).unitRoute = P.unitRoute := by
  cases hp
  cases hq
  rfl

private theorem unitRoute_listPath {width span : ℕ} (r : List (Point width span))
    (hne : r ≠ []) (hc : r.IsChain (fun p q => step p q = true)) (hn : r.Nodup) :
    (listPath r hne hc).unitRoute = r.map point := by
  have hp : (PushPuzzle.NCL.GridRouting.Path.unitWalk (listPath r hne hc)).IsPath := by
    rw [SimpleGraph.Walk.isPath_def, support_listPath]
    exact hn.map (point_injective width span)
  change (PushPuzzle.NCL.GridRouting.Path.unitWalk (listPath r hne hc)).bypass.support = _
  rw [hp.bypass_eq_self, support_listPath]

private theorem route_chain {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    P.route.IsChain (fun p q => step p q = true) := by
  obtain ⟨_, _, _, _, hc, hy⟩ := P.route_spec h
  rw [List.isChain_iff_getElem]
  intro i hi
  exact decide_eq_true ⟨(List.isChain_iff_getElem.mp hc) i hi,
    (List.isChain_iff_getElem.mp hy.isChain) i hi⟩

/-- The selected downward route as an actual finite horizontal/downward-vertical grid path. -/
def Pattern.gridPath {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    GridRouting.Path (gridPoint P.source) (gridPoint P.target) :=
  let spec := P.route_spec h
  let hne : P.route ≠ [] := by intro he; simp [he] at spec
  (listPath P.route hne (route_chain P h)).cast
    (congrArg gridPoint (List.head_of_head?_eq_some spec.1))
    (congrArg gridPoint (List.getLast_of_getLast?_eq_some spec.2.1))

/-- Normalizing this actual grid path returns the same original selected integer point list. -/
theorem Pattern.gridPath_unitRoute {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    (P.gridPath h).unitRoute = P.integerRoute := by
  unfold PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath
  rw [unitRoute_cast, unitRoute_listPath]
  · rfl
  · exact (P.route_spec h).2.2.1

/-- The actual selected grid path already traverses precisely its original integer point list. -/
theorem Pattern.gridPath_unitWalk {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points step
      (fun p => p == P.source) (fun p => p == P.target) r) :
    (PushPuzzle.NCL.GridRouting.Path.unitWalk (P.gridPath h)).support = P.integerRoute := by
  unfold PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath
  erw [support_unitWalk_cast, support_listPath]
  rfl

/-- Every lattice point of the selected actual grid path is an original marked window point. -/
theorem Pattern.gridPath_points {width span : ℕ} (P : Pattern width span)
    (h : ∃ r, Cslib.Reachability.IsSrcTgtWalk P.points step
      (fun p => p == P.source) (fun p => p == P.target) r)
    (x : GridRouting.Point) (hx : (P.gridPath h).Contains x) :
    ∃ q, P.marked q.1 q.2 = true ∧ gridPoint q = x := by
  unfold PushPuzzle.NCL.GridDrawing.WindowRoute.Pattern.gridPath at hx
  erw [GridRouting.Path.contains_cast_iff, contains_listPath] at hx
  obtain ⟨q, hq, rfl⟩ := hx
  exact ⟨q, (P.route_spec h).2.2.2.1 q hq, rfl⟩

end PushPuzzle.NCL.GridDrawing.WindowRoute

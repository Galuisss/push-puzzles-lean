/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.RoutingMetadata
public import PushS.Source.Strip.Sweep.Arcs
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Actual carrier/unit-index records

Enumerate each complete carrier's consecutive point pairs and retain the original carrier and
unit indices. The standard encoded list scan is polynomial-time, and on the actual full carrier
arrays it returns exactly the original sweep's finite unit-arc enumeration.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.UnitSegment`: one original edge/unit index with its actual ordered endpoints.
* `PushPuzzle.NCL.Strip.PolyTime.segments`: the indexed consecutive-pair list scan.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.computableInPolyTime_segments`: standard encoded segment record emission.
* `PushPuzzle.NCL.Strip.PolyTime.segments_ofFn`: exact agreement with the actual sweep arc list.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- An original carrier/unit index together with that occurrence's ordered grid endpoints. -/
structure UnitSegment where
  /-- Original carrier index. -/
  edge : ℕ
  /-- Original consecutive-pair position within the carrier. -/
  index : ℕ
  /-- Actual endpoint first visited along the original carrier. -/
  start : Point
  /-- Actual endpoint visited next along the original carrier. -/
  finish : Point

/-- Unary carrier/unit indices and standard signed-unary grid endpoints. -/
enc_structure encUnitSegment : UnitSegment where
  edge : encUnary, index : encUnary, start : encPoint, finish : encPoint

/-- Enumerate the actual consecutive point pairs in original carrier and unit-index order. -/
@[expose] def segments (routes : List Route) : List UnitSegment :=
  routes.zipIdx.flatMap fun (route, edge) =>
    route.consecutivePairs.zipIdx.map fun (points, index) =>
      { edge := edge, index := index, start := points.1, finish := points.2 }

/-- Emit the original edge/unit-index records in standard polynomial time. -/
theorem computableInPolyTime_segments :
    ComputableInPolyTime segments (encList encRoute) (encList encUnitSegment) := by
  have hz : ComputableInPolyTime (fun routes : List Route => routes.zipIdx)
      (encList encRoute) (encList (encPair encRoute encUnary)) := by fun_prop
  have hp : ComputableInPolyTime (fun p : List Route × (Route × ℕ) =>
      p.2.1.consecutivePairs.zipIdx)
      (encPair (encList encRoute) (encPair encRoute encUnary))
      (encList (encPair (encPair encPoint encPoint) encUnary)) := by fun_prop
  unfold segments
  apply ComputableInPolyTime.flatMapWithInput hz
  apply ComputableInPolyTime.mapWithInput hp
  fun_prop

/-- Read the same original index and ordered endpoints from an actual typed unit-arc label. -/
@[expose] def UnitSegment.ofArc {V : Type*} {m A K : ℕ} (R : Environment V (Fin m) A K)
    (a : PushPuzzle.NCL.Strip.Sweep.Arc R) : UnitSegment where
  edge := a.edge.val
  index := a.index.val
  start := (a.pair R).1
  finish := (a.pair R).2

private theorem zipIdx_ofFn {α : Type*} {n : ℕ} (f : Fin n → α) :
    (List.ofFn f).zipIdx = List.ofFn (fun i : Fin n => (f i, i.val)) := by
  apply List.ext_getElem
  · simp
  intro i hi hj
  simp

private theorem zipIdx_eq_ofFn {α : Type*} (xs : List α) :
    xs.zipIdx = List.ofFn (fun i : Fin xs.length => (xs.get i, i.val)) := by
  have h := zipIdx_ofFn xs.get
  simpa only [List.ofFn_get] using h

/-- Indexed pair emission returns the same complete actual sweep arcs, in the same order. -/
theorem segments_ofFn {V : Type*} {m A K : ℕ} (R : Environment V (Fin m) A K) :
    segments (List.ofFn R.unitRoute) =
      (PushPuzzle.NCL.Strip.Sweep.arcs R (List.finRange m)).map (PushPuzzle.NCL.Strip.PolyTime.UnitSegment.ofArc R) := by
  unfold segments PushPuzzle.NCL.Strip.Sweep.arcs
  rw [zipIdx_ofFn, List.ofFn_eq_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  intro e _
  dsimp only
  rw [zipIdx_eq_ofFn, List.map_ofFn, List.map_ofFn]
  rfl

end PushPuzzle.NCL.Strip.PolyTime

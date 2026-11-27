/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.ArcData
public import PushS.Source.Strip.Sweep.Scan
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Div

/-!
# Standard encoded actual local sweep slices

Filter the two consecutive actual carrier-array frontiers at the decoded nonnegative grid site.
The resulting explicit context and local port records are polynomial-time and agree exactly
with the same actual original sweep slice.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.SliceData`: original indexed arcs in the four actual slice blocks.
* `PushPuzzle.NCL.Strip.PolyTime.SliceData.ofRoutes`: the standard encoded local slice algorithm.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.SliceData.computableInPolyTime_ofRoutes`: actual polynomial-time slices.
* `PushPuzzle.NCL.Strip.PolyTime.SliceData.ofRoutes_ofFn`: exact original local slice agreement.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- The actual unchanged context and local port blocks, retaining original unit-arc identities.
-/
@[ext] structure SliceData where
  /-- Actual unchanged higher frontier arcs. -/
  above : List ArcData
  /-- Actual arcs ending at the processed grid site. -/
  incoming : List ArcData
  /-- Actual arcs beginning at the processed grid site. -/
  outgoing : List ArcData
  /-- Actual unchanged lower frontier arcs. -/
  below : List ArcData

/-- Four standard framed lists of the actual indexed canonical arc records. -/
enc_structure encSliceData : SliceData where
  above : (encList encArcData), incoming : (encList encArcData),
  outgoing : (encList encArcData), below : (encList encArcData)

namespace SliceData

open Cslib.Complexity Cslib.Complexity.NCL

/-- Decode a nonnegative scan index into its actual column-major natural grid site. -/
@[expose] def scanPoint (K t : ℕ) : ℕ × ℕ := (t / (PushPuzzle.NCL.Strip.Sweep.height K + 1), t % (PushPuzzle.NCL.Strip.Sweep.height K + 1))

/-- The actual nonnegative grid decoder is standard encoded polynomial-time. -/
@[fun_prop] theorem computableInPolyTime_scanPoint (K : ℕ) :
    ComputableInPolyTime (scanPoint K) encUnary encNatPoint := by
  unfold scanPoint
  fun_prop

/-- The natural decoder is the same actual original integer scan point. -/
theorem integer_scanPoint (K t : ℕ) :
    (((scanPoint K t).1 : ℤ), ((scanPoint K t).2 : ℤ)) = PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ) := rfl

/-- Read the four actual local blocks directly from the complete original carrier arrays. -/
@[expose] def ofRoutes (K : ℕ) (routes : List Route) (t : ℕ) : SliceData :=
  let p := scanPoint K t
  let before := PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier K routes t
  let after := PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier K routes (t + 1)
  { above := before.filter (fun a => decide (2 * p.2 + 1 < a.position))
    incoming := before.filter (fun a => decide (a.upper = p))
    outgoing := after.filter (fun a => decide (a.lower = p))
    below := before.filter (fun a => decide (a.position + 2 ≤ 2 * p.2)) }

/-- The actual local carrier-array slice is polynomial-time under the standard encoding. -/
theorem computableInPolyTime_ofRoutes (K : ℕ) :
    ComputableInPolyTime (fun p : List Route × ℕ => ofRoutes K p.1 p.2)
      (encPair (encList encRoute) encUnary) encSliceData := by
  have hb := PushPuzzle.NCL.Strip.PolyTime.ArcData.computableInPolyTime_frontier K
  have ha : ComputableInPolyTime (fun p : List Route × ℕ => PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier K p.1 (p.2 + 1))
      (encPair (encList encRoute) encUnary) (encList encArcData) := by
    simpa only [Function.comp_def] using hb.comp
      (show ComputableInPolyTime (fun p : List Route × ℕ => (p.1, p.2 + 1))
        (encPair (encList encRoute) encUnary) (encPair (encList encRoute) encUnary) from by
          fun_prop)
  unfold ofRoutes
  apply encSliceData_mk_polyTime
  · apply ComputableInPolyTime.filterWithInput hb
    unfold PushPuzzle.NCL.Strip.PolyTime.ArcData.position
    fun_prop
  · apply ComputableInPolyTime.filterWithInput hb
    fun_prop
  · apply ComputableInPolyTime.filterWithInput ha
    fun_prop
  · apply ComputableInPolyTime.filterWithInput hb
    unfold PushPuzzle.NCL.Strip.PolyTime.ArcData.position
    fun_prop

variable {V : Type*} {m A K : ℕ} (R : Environment V (Fin m) A K)

/-- Record the same original typed slice's actual canonical arcs. -/
@[expose] def ofSlice (s : PushPuzzle.NCL.Strip.Sweep.Slice R) : SliceData where
  above := s.above.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R)
  incoming := s.incoming.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R)
  outgoing := s.outgoing.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R)
  below := s.below.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R)

private theorem upper_eq_scanPoint (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R a).upper = scanPoint K t ↔ a.upper R = PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ) := by
  rw [← PushPuzzle.NCL.Strip.PolyTime.ArcData.integer_upper_ofArc R a, ← integer_scanPoint K t]
  simp only [Prod.ext_iff, Int.natCast_inj]

private theorem lower_eq_scanPoint (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R a).lower = scanPoint K t ↔ a.lower R = PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ) := by
  rw [← PushPuzzle.NCL.Strip.PolyTime.ArcData.integer_lower_ofArc R a, ← integer_scanPoint K t]
  simp only [Prod.ext_iff, Int.natCast_inj]

private theorem above_iff (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    2 * (scanPoint K t).2 + 1 < (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R a).position ↔
      2 * (PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ)).2 + 1 < a.position R := by
  have hp := PushPuzzle.NCL.Strip.PolyTime.ArcData.integer_position_ofArc R a
  have hy := congrArg Prod.snd (integer_scanPoint K t)
  omega

private theorem below_iff (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R a).position + 2 ≤ 2 * (scanPoint K t).2 ↔
      a.position R ≤ 2 * (PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ)).2 - 2 := by
  have hp := PushPuzzle.NCL.Strip.PolyTime.ArcData.integer_position_ofArc R a
  have hy := congrArg Prod.snd (integer_scanPoint K t)
  omega

/-- The standard encoded local records are exactly the same actual original sweep slice. -/
theorem ofRoutes_ofFn (t : ℕ) :
    ofRoutes K (List.ofFn R.unitRoute) t =
      ofSlice R (PushPuzzle.NCL.Strip.Sweep.slice R (List.finRange m) (PushPuzzle.NCL.Strip.Sweep.scanPoint K (t : ℤ))) := by
  unfold ofRoutes ofSlice
  rw [PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier_ofFn, PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier_ofFn]
  simp only [PushPuzzle.NCL.Strip.Sweep.slice, PushPuzzle.NCL.Strip.Sweep.level_scanPoint, Nat.cast_add, Nat.cast_one]
  apply PushPuzzle.NCL.Strip.PolyTime.SliceData.ext
  all_goals dsimp only
  all_goals rw [List.filter_map]
  all_goals apply congrArg (List.map (PushPuzzle.NCL.Strip.PolyTime.ArcData.ofArc R))
  all_goals apply List.filter_congr
  all_goals intro a _
  · exact decide_eq_decide.mpr (above_iff R a t)
  · exact decide_eq_decide.mpr (upper_eq_scanPoint R a t)
  · exact decide_eq_decide.mpr (lower_eq_scanPoint R a t)
  · exact decide_eq_decide.mpr (below_iff R a t)

end SliceData
end PushPuzzle.NCL.Strip.PolyTime

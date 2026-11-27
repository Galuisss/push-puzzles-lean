/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.UnitRoute
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Polynomial-time bounded subdivision of actual carriers

Use the existing signed-unary integer encoding for explicit grid coordinates. The actual
bounded subdivision enumerates unit-prefix points on each listed segment and then its final
endpoint. Its standard encoded implementation computes the same full carrier unit route under
the already proved fixed carrier wire budget.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.encPoint`, `PushPuzzle.NCL.Strip.PolyTime.encRoute`: signed-unary geometric data encodings.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.computableInPolyTime_subdivideWithin`: actual bounded subdivision is PT.
The actual-carrier caller uses `PushPuzzle.NCL.Strip.Environment.subdivideWithin_route_eq`.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- A mathematical grid coordinate pair, with both signed coordinates in unary. -/
abbrev encPoint : Point ↪ List Bool := encPair encIntUnary encIntUnary

/-- The explicit point list of a route, framed over the signed-unary coordinate pairs. -/
abbrev encRoute : Route ↪ List Bool := encList encPoint

@[local fun_prop]
private theorem computableInPolyTime_intAdd :
    ComputableInPolyTime (fun p : ℤ × ℤ => p.1 + p.2)
      (encPair encIntUnary encIntUnary) encIntUnary := by
  have h : ComputableInPolyTime (fun p : ℤ × ℤ => p.1 - (0 - p.2))
      (encPair encIntUnary encIntUnary) encIntUnary := by fun_prop
  simpa only [zero_sub, sub_neg_eq_add] using h

@[local fun_prop]
private theorem computableInPolyTime_intLt :
    ComputableInPolyTime (fun p : ℤ × ℤ => decide (p.1 < p.2))
      (encPair encIntUnary encIntUnary) encBool := by
  have hs : ComputableInPolyTime (fun p : ℤ × ℤ => p.2 - p.1)
      (encPair encIntUnary encIntUnary) encIntUnary := by fun_prop
  simpa only [Function.comp_def, sub_pos] using ComputableInPolyTime.int_pos.comp hs

@[local fun_prop]
private theorem computableInPolyTime_length :
    ComputableInPolyTime (fun p : Point × Point => length p.1 p.2)
      (encPair encPoint encPoint) encUnary := by
  unfold length
  fun_prop

private theorem step_eq (a b : Point) (i : ℕ) : a + i • direction a b =
    if a.1 < b.1 then (a.1 + i, a.2)
    else if b.1 < a.1 then (a.1 - i, a.2)
    else if a.2 < b.2 then (a.1, a.2 + i)
    else (a.1, a.2 - i) := by
  simp only [direction]
  split_ifs <;> ext <;> simp [Prod.smul_mk, sub_eq_add_neg]

@[local fun_prop]
private theorem computableInPolyTime_step :
    ComputableInPolyTime (fun p : (Point × Point) × ℕ => p.1.1 + p.2 • direction p.1.1 p.1.2)
      (encPair (encPair encPoint encPoint) encUnary) encPoint := by
  simp only [step_eq]
  have hx : ComputableInPolyTime (fun p : (Point × Point) × ℕ => p.1.1.1)
      (encPair (encPair encPoint encPoint) encUnary) encIntUnary := by fun_prop
  have hy : ComputableInPolyTime (fun p : (Point × Point) × ℕ => p.1.1.2)
      (encPair (encPair encPoint encPoint) encUnary) encIntUnary := by fun_prop
  have hX : ComputableInPolyTime (fun p : (Point × Point) × ℕ => p.1.2.1)
      (encPair (encPair encPoint encPoint) encUnary) encIntUnary := by fun_prop
  have hY : ComputableInPolyTime (fun p : (Point × Point) × ℕ => p.1.2.2)
      (encPair (encPair encPoint encPoint) encUnary) encIntUnary := by fun_prop
  have hi := ComputableInPolyTime.int_natCast.comp
    (ComputableInPolyTime.snd (encPair encPoint encPoint) encUnary)
  have hxpos := (computableInPolyTime_intAdd.comp (hx.prod hi)).prod hy
  have hxneg := (ComputableInPolyTime.int_sub.comp (hx.prod hi)).prod hy
  have hypos := hx.prod (computableInPolyTime_intAdd.comp (hy.prod hi))
  have hyneg := hx.prod (ComputableInPolyTime.int_sub.comp (hy.prod hi))
  have hxy := computableInPolyTime_intLt.comp (hx.prod hX)
  have hyx := computableInPolyTime_intLt.comp (hX.prod hx)
  have hyy := computableInPolyTime_intLt.comp (hy.prod hY)
  simpa only [Function.comp_def, decide_eq_true_eq] using
    hxy.ite' hxpos (hyx.ite' hxneg (hyy.ite' hypos hyneg))

private theorem computableInPolyTime_segmentPrefix (budget : ℕ) :
    ComputableInPolyTime (fun p : Point × Point =>
      (List.range (min (length p.1 p.2) budget)).map (fun i => p.1 + i • direction p.1 p.2))
      (encPair encPoint encPoint) encRoute := by
  apply ComputableInPolyTime.mapWithInput
  · fun_prop
  · exact computableInPolyTime_step

/-- Enumerate actual consecutive point pairs in polynomial time under the route encoding. -/
@[fun_prop]
theorem computableInPolyTime_consecutivePairs :
    ComputableInPolyTime List.consecutivePairs encRoute (encList (encPair encPoint encPoint)) := by
  unfold List.consecutivePairs
  fun_prop

private theorem computableInPolyTime_lastPoint :
    ComputableInPolyTime (fun r : Route => r.getLast?.toList) encRoute encRoute := by
  have h : ComputableInPolyTime (fun r : Route => r.reverse.take 1) encRoute encRoute := by
    fun_prop
  simpa only [List.take_one, List.getLast?_eq_head?_reverse] using h

/-- The existing bounded geometric subdivision is polynomial-time under explicit standard codes.
-/
theorem computableInPolyTime_subdivideWithin (budget : ℕ) :
    ComputableInPolyTime (subdivideWithin budget) encRoute encRoute := by
  have hp : ComputableInPolyTime (fun r : Route =>
      r.consecutivePairs.flatMap (fun e =>
        (List.range (min (length e.1 e.2) budget)).map
          (fun i => e.1 + i • direction e.1 e.2))) encRoute encRoute := by
    apply ComputableInPolyTime.flatMapWithInput computableInPolyTime_consecutivePairs
    simpa only [Function.comp_def] using (computableInPolyTime_segmentPrefix budget).comp
      (ComputableInPolyTime.snd encRoute (encPair encPoint encPoint))
  unfold subdivideWithin
  simpa only [Function.comp_def] using (ComputableInPolyTime.listAppend encPoint).comp
    (hp.prod computableInPolyTime_lastPoint)

end PushPuzzle.NCL.Strip.PolyTime

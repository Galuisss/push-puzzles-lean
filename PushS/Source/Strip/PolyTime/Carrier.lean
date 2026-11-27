/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.Subdivision
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List

/-!
# Standard encoded actual six-point carriers

An explicit carrier record contains its actual track, two flattened vertex addresses, and two
original port slots. Route emission and bounded unit subdivision are polynomial-time. Reading
these fields from the existing environment recovers exactly its complete actual unit route.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.Carrier`: explicit actual carrier input metadata.
* `PushPuzzle.NCL.Strip.PolyTime.Carrier.route`, `.unitRoute`: actual six-point and bounded unit emission.
* `PushPuzzle.NCL.Strip.PolyTime.Carrier.ofEnvironment`: same fields from the original routing environment.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.Carrier.computableInPolyTime_unitRoute`: standard encoded carrier compilation.
* `PushPuzzle.NCL.Strip.PolyTime.Carrier.unitRoute_ofEnvironment`: exact full carrier agreement.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- The actual geometric data selecting one original six-point carrier. -/
structure Carrier where
  /-- Actual horizontal track. -/
  track : ℕ
  /-- Flattened address of the original false endpoint. -/
  source : ℕ
  /-- Flattened address of the original true endpoint. -/
  target : ℕ
  /-- Original port-list slot at the false endpoint. -/
  sourcePort : Fin 3
  /-- Original port-list slot at the true endpoint. -/
  targetPort : Fin 3

/-- Unary track/addresses and standard fixed finite port slots. -/
enc_structure encCarrier : Carrier where
  track : encUnary, source : encUnary, target : encUnary,
  sourcePort : (encFinEnum (Fin 3)), targetPort : (encFinEnum (Fin 3))

namespace Carrier

open Cslib.Complexity Cslib.Complexity.NCL

/-- Emit the same existing six-point track carrier from explicit metadata. -/
@[expose] def route (c : Carrier) : Route :=
  PushPuzzle.NCL.Strip.Tracks.route c.track c.source c.target c.sourcePort c.targetPort

/-- Emit the existing bounded subdivision of the same carrier. -/
@[expose] def unitRoute (budget : ℕ) (c : Carrier) : Route := subdivideWithin budget c.route

private theorem computableInPolyTime_column :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => PushPuzzle.NCL.Strip.Tracks.column p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encIntUnary := by
  have hv := ComputableInPolyTime.of_finite (encIn := encFinEnum (Fin 3)) (encOut := encUnary)
    (fun s : Fin 3 => s.val)
  have h : ComputableInPolyTime (fun p : ℕ × Fin 3 => ((8 * p.1 + 2 * p.2.val + 2 : ℕ) : ℤ))
      (encPair encUnary (encFinEnum (Fin 3))) encIntUnary := by fun_prop
  change ComputableInPolyTime (fun p : ℕ × Fin 3 => 8 * (p.1 : ℤ) + 2 * (p.2.val : ℤ) + 2) _ _
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

private theorem computableInPolyTime_center :
    ComputableInPolyTime PushPuzzle.NCL.Strip.Tracks.center encUnary encPoint := by
  have h : ComputableInPolyTime (fun v : ℕ => (((8 * v + 4 : ℕ) : ℤ), (4 : ℤ)))
      encUnary encPoint := by fun_prop
  change ComputableInPolyTime (fun v : ℕ => (8 * (v : ℤ) + 4, 4)) _ _
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

private theorem computableInPolyTime_elbow :
    ComputableInPolyTime (fun p : ℕ × Fin 3 => PushPuzzle.NCL.Strip.Tracks.elbow p.1 p.2)
      (encPair encUnary (encFinEnum (Fin 3))) encPoint := by
  have hh : ComputableInPolyTime (fun s : Fin 3 => (4 : ℤ) + if s = 1 then 2 else 0)
      (encFinEnum (Fin 3)) encIntUnary := ComputableInPolyTime.of_finite _
  simpa only [Function.comp_def, PushPuzzle.NCL.Strip.Tracks.elbow] using
    computableInPolyTime_column.prod (hh.comp (ComputableInPolyTime.snd _ _))

private theorem computableInPolyTime_rail :
    ComputableInPolyTime PushPuzzle.NCL.Strip.Tracks.rail encUnary encIntUnary := by
  have h : ComputableInPolyTime (fun k : ℕ => ((10 + 2 * k : ℕ) : ℤ))
      encUnary encIntUnary := by fun_prop
  change ComputableInPolyTime (fun k : ℕ => 10 + 2 * (k : ℤ)) _ _
  simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using h

/-- The original six-point track carrier emits in standard polynomial time. -/
private theorem computableInPolyTime_route : ComputableInPolyTime route encCarrier encRoute := by
  have hs := computableInPolyTime_center.comp (encCarrier_source_polyTime ComputableInPolyTime.id')
  have ht := computableInPolyTime_center.comp (encCarrier_target_polyTime ComputableInPolyTime.id')
  have hsp : ComputableInPolyTime (fun c : Carrier => (c.source, c.sourcePort)) encCarrier
      (encPair encUnary (encFinEnum (Fin 3))) := by fun_prop
  have htp : ComputableInPolyTime (fun c : Carrier => (c.target, c.targetPort)) encCarrier
      (encPair encUnary (encFinEnum (Fin 3))) := by fun_prop
  have hse := computableInPolyTime_elbow.comp hsp
  have hte := computableInPolyTime_elbow.comp htp
  have hsc := computableInPolyTime_column.comp hsp
  have htc := computableInPolyTime_column.comp htp
  have hr := computableInPolyTime_rail.comp (encCarrier_track_polyTime ComputableInPolyTime.id')
  unfold route PushPuzzle.NCL.Strip.Tracks.route
  fun_prop

/-- The actual bounded carrier compiler is polynomial-time under standard explicit codes. -/
theorem computableInPolyTime_unitRoute (budget : ℕ) :
    ComputableInPolyTime (unitRoute budget) encCarrier encRoute :=
  (computableInPolyTime_subdivideWithin budget).comp computableInPolyTime_route

/-- Read the actual six-point geometric input fields from the original environment. -/
@[expose] def ofEnvironment {V E : Type*} {A K : ℕ} (R : Environment V E A K) (e : E) :
    Carrier where
  track := R.track e
  source := R.vertices.address (R.endpoint e false)
  target := R.vertices.address (R.endpoint e true)
  sourcePort := R.port e false
  targetPort := R.port e true

/-- The standard encoded bounded compiler returns the same complete original carrier traversal.
-/
theorem unitRoute_ofEnvironment {V E : Type*} {A K : ℕ} (R : Environment V E A K) (e : E) :
    unitRoute (PushPuzzle.NCL.Strip.Environment.routeBudget A K) (ofEnvironment R e) = R.unitRoute e :=
  R.subdivideWithin_route_eq e

end Carrier
end PushPuzzle.NCL.Strip.PolyTime

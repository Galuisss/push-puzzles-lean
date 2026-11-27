/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.PolyTime.Segments
public import PushS.Source.Strip.Sweep.FrontierData
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Int
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Mathlib.Tactic.Linarith

/-!
# Standard encoded geometric unit-arc records

The actual carriers occupy nonnegative grid sites. Convert their indexed unit segments to
canonical lower/upper natural coordinates, retain the original unit direction bit, and scan
their fixed geometric frontier keys. Each operation is polynomial-time under the standard
encodings; the result is exactly the original frontier's actual indexed unit arcs.

## Main definitions

* `PushPuzzle.NCL.Strip.PolyTime.ArcData`: original carrier/unit index with canonical grid endpoints.
* `PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier`: standard encoded actual carrier-array frontier computation.

## Main results

* `PushPuzzle.NCL.Strip.PolyTime.ArcData.computableInPolyTime_frontier`: standard encoded PT frontier scan.
* `PushPuzzle.NCL.Strip.PolyTime.ArcData.frontier_ofFn`: exact actual sweep frontier agreement.
-/

public section

namespace PushPuzzle.NCL.Strip.PolyTime

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal _root_.Turing.MultiTapeTM

/-- A nonnegative mathematical grid-coordinate pair, with both coordinates in unary. -/
abbrev encNatPoint : (ℕ × ℕ) ↪ List Bool := encPair encUnary encUnary

/-- Actual original unit-arc identity, canonical endpoints, and traversal direction. -/
structure ArcData where
  /-- Original carrier index. -/
  edge : ℕ
  /-- Original unit-segment index. -/
  index : ℕ
  /-- Coordinatewise lower canonical grid endpoint. -/
  lower : ℕ × ℕ
  /-- Coordinatewise upper canonical grid endpoint. -/
  upper : ℕ × ℕ
  /-- Whether the original ordered segment runs from upper to lower. -/
  reversed : Bool

/-- Standard record encoding with unary original indices and canonical natural coordinates. -/
enc_structure encArcData : ArcData where
  edge : encUnary, index : encUnary, lower : encNatPoint, upper : encNatPoint, reversed : encBool

namespace ArcData

open Cslib.Complexity Cslib.Complexity.NCL

/-- Canonicalize the actual ordered endpoints while retaining original indices and direction. -/
@[expose] def ofSegment (s : UnitSegment) : ArcData :=
  let lower := (min s.start.1.toNat s.finish.1.toNat, min s.start.2.toNat s.finish.2.toNat)
  let upper := (max s.start.1.toNat s.finish.1.toNat, max s.start.2.toNat s.finish.2.toNat)
  { edge := s.edge, index := s.index, lower := lower, upper := upper,
    reversed := decide ((s.start.1.toNat, s.start.2.toNat) = upper) }

/-- Standard encoded canonicalization of one original unit-segment record. -/
private theorem computableInPolyTime_ofSegment :
    ComputableInPolyTime ofSegment encUnitSegment encArcData := by
  unfold ofSegment
  fun_prop

/-- Geometric key of an actual canonical arc, in the same decreasing frontier order. -/
@[expose] def position (a : ArcData) : ℕ :=
  if a.lower.2 = a.upper.2 then 2 * a.lower.2 else 2 * a.upper.2 - 1

/-- Nonnegative column-major scan position of a canonical grid endpoint. -/
@[expose] def scanLevel (K : ℕ) (p : ℕ × ℕ) : ℕ := (PushPuzzle.NCL.Strip.Sweep.height K + 1) * p.1 + p.2

/-- Whether the actual nonnegative scan cut meets this canonical arc. -/
@[expose] def Active (K t : ℕ) (a : ArcData) : Prop :=
  scanLevel K a.lower < t ∧ t ≤ scanLevel K a.upper

instance (K t : ℕ) (a : ArcData) : Decidable (Active K t a) := inferInstanceAs (Decidable (_ ∧ _))

/-- Explicit candidate metadata of the same actual canonical arc at a scan cut. -/
@[expose] def toEntry (K t : ℕ) (a : ArcData) : PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry ArcData :=
  ⟨a, decide (Active K t a), a.position⟩

/-- Canonicalize the complete actual indexed carrier-segment enumeration. -/
@[expose] def records (routes : List Route) : List ArcData := (segments routes).map ofSegment

/-- Rebase the original carrier direction by this actual unit segment's traversal reversal. -/
@[expose] def direction (bits : List Bool) (a : ArcData) : Bool :=
  a.reversed ^^ bits.getD a.edge false

/-- Read the actual original direction and its unit-arc rebasing in standard polynomial time. -/
@[fun_prop] theorem computableInPolyTime_direction :
    ComputableInPolyTime (fun p : List Bool × ArcData => direction p.1 p.2)
      (encPair (encList encBool) encArcData) encBool := by
  have hx : ComputableInPolyTime (fun p : Bool × Bool => p.1 ^^ p.2)
      (encPair encBool encBool) encBool := ComputableInPolyTime.of_finite _
  have hp : ComputableInPolyTime (fun p : List Bool × ArcData =>
      (p.2.reversed, p.1.getD p.2.edge false))
      (encPair (encList encBool) encArcData) (encPair encBool encBool) := by fun_prop
  exact (hx.comp hp).of_enc_eq (fun _ => rfl)

/-- Compute the same actual ordered frontier from explicit complete carrier point arrays. -/
@[expose] def frontier (K : ℕ) (routes : List Route) (t : ℕ) : List ArcData :=
  PushPuzzle.NCL.Strip.Sweep.FrontierData.scan (2 * PushPuzzle.NCL.Strip.Sweep.height K + 1) ((records routes).map (toEntry K t))

/-- Standard encoded canonical carrier records emit in polynomial time. -/
private theorem computableInPolyTime_records :
    ComputableInPolyTime records (encList encRoute) (encList encArcData) :=
  (ComputableInPolyTime.map computableInPolyTime_ofSegment).comp computableInPolyTime_segments

private theorem computableInPolyTime_toEntry (K : ℕ) :
    ComputableInPolyTime (fun p : ℕ × ArcData => toEntry K p.1 p.2)
      (encPair encUnary encArcData) (PushPuzzle.NCL.Strip.Sweep.FrontierData.encEntry ArcData encArcData) := by
  unfold toEntry
  apply PushPuzzle.NCL.Strip.Sweep.FrontierData.encEntry_mk_polyTime ArcData encArcData
  · exact ComputableInPolyTime.snd _ _
  · unfold Active scanLevel
    fun_prop
  · unfold position
    fun_prop

/-- The complete actual carrier-array frontier computation is standard encoded polynomial-time.
-/
theorem computableInPolyTime_frontier (K : ℕ) :
    ComputableInPolyTime (fun p : List Route × ℕ => frontier K p.1 p.2)
      (encPair (encList encRoute) encUnary) (encList encArcData) := by
  have hr := computableInPolyTime_records.comp
    (ComputableInPolyTime.fst (encList encRoute) encUnary)
  have he : ComputableInPolyTime (fun p : List Route × ℕ => (records p.1).map (toEntry K p.2))
      (encPair (encList encRoute) encUnary)
      (encList (PushPuzzle.NCL.Strip.Sweep.FrontierData.encEntry ArcData encArcData)) := by
    apply ComputableInPolyTime.mapWithInput hr
    simpa only [Function.comp_def] using (computableInPolyTime_toEntry K).comp
      (show ComputableInPolyTime (fun p : (List Route × ℕ) × ArcData => (p.1.2, p.2))
        (encPair (encPair (encList encRoute) encUnary) encArcData)
        (encPair encUnary encArcData) from by fun_prop)
  unfold frontier
  simpa only [Function.comp_def] using
    (PushPuzzle.NCL.Strip.Sweep.FrontierData.computableInPolyTime_scan encArcData (2 * PushPuzzle.NCL.Strip.Sweep.height K + 1)).comp he

variable {V : Type*} {m A K : ℕ} (R : Environment V (Fin m) A K)

/-- The canonical standard record of the same original typed unit-arc label. -/
@[expose] def ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) : ArcData := ofSegment (PushPuzzle.NCL.Strip.PolyTime.UnitSegment.ofArc R a)

private theorem toNat_min (a b : ℤ) : min a.toNat b.toNat = (min a b).toNat := by omega

private theorem toNat_max (a b : ℤ) : max a.toNat b.toNat = (max a b).toNat := by omega

private theorem lower_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (ofArc R a).lower = ((a.lower R).1.toNat, (a.lower R).2.toNat) := by
  simp only [ofArc, ofSegment, PushPuzzle.NCL.Strip.PolyTime.UnitSegment.ofArc, PushPuzzle.NCL.Strip.Sweep.Arc.lower, toNat_min]

private theorem upper_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (ofArc R a).upper = ((a.upper R).1.toNat, (a.upper R).2.toNat) := by
  simp only [ofArc, ofSegment, PushPuzzle.NCL.Strip.PolyTime.UnitSegment.ofArc, PushPuzzle.NCL.Strip.Sweep.Arc.upper, toNat_max]

private theorem endpoint_nonnegative (e : Fin m) {p : Point}
    (hp : realPoint p ∈ support (R.route e)) : 0 ≤ p.1 ∧ 0 ≤ p.2 := by
  have h := R.support_window e hp
  have hr : (0 : ℝ) ≤ 8 * (A : ℝ) * R.edges.row e := by positivity
  have hx : (0 : ℝ) ≤ p.1 := by dsimp only [realPoint] at h; linarith [h.1]
  have hy : (0 : ℝ) ≤ p.2 := by dsimp only [realPoint] at h; linarith [h.2.2.1]
  exact_mod_cast And.intro hx hy

/-- Casting the actual canonical lower natural coordinate recovers the original integer site. -/
theorem integer_lower_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (((ofArc R a).lower.1 : ℤ), ((ofArc R a).lower.2 : ℤ)) = a.lower R := by
  rw [lower_ofArc]
  have hp := endpoint_nonnegative R a.edge (a.canonical_endpoints_mem R).1
  exact Prod.ext (Int.toNat_of_nonneg hp.1) (Int.toNat_of_nonneg hp.2)

/-- Casting the actual canonical upper natural coordinate recovers the original integer site. -/
theorem integer_upper_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (((ofArc R a).upper.1 : ℤ), ((ofArc R a).upper.2 : ℤ)) = a.upper R := by
  rw [upper_ofArc]
  have hp := endpoint_nonnegative R a.edge (a.canonical_endpoints_mem R).2
  exact Prod.ext (Int.toNat_of_nonneg hp.1) (Int.toNat_of_nonneg hp.2)

/-- Standard-data traversal rebasing is the actual original unit-arc direction bit. -/
private theorem reversed_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (ofArc R a).reversed = a.reversed R := by
  change decide (((a.pair R).1.1.toNat, (a.pair R).1.2.toNat) = (ofArc R a).upper) = _
  rw [upper_ofArc]
  unfold PushPuzzle.NCL.Strip.Sweep.Arc.reversed
  apply decide_eq_decide.mpr
  have hp := endpoint_nonnegative R a.edge (a.endpoints_mem R).1
  have hu := endpoint_nonnegative R a.edge (a.canonical_endpoints_mem R).2
  simp only [Prod.ext_iff]
  omega

/-- Encoded records retain the same actual source-bit reading and original unit reversal. -/
theorem direction_ofArc (bits : List Bool) (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    direction bits (ofArc R a) = (a.reversed R ^^ bits.getD a.edge.val false) := by
  unfold direction
  rw [reversed_ofArc]
  rfl

private theorem scanLevel_toNat (p : Point) (hp : 0 ≤ p.1 ∧ 0 ≤ p.2) :
    (scanLevel K (p.1.toNat, p.2.toNat) : ℤ) = PushPuzzle.NCL.Strip.Sweep.level K p := by
  simp only [scanLevel, PushPuzzle.NCL.Strip.Sweep.level, Nat.cast_add, Nat.cast_mul,
    Int.toNat_of_nonneg hp.1, Int.toNat_of_nonneg hp.2]

private theorem active_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    Active K t (ofArc R a) ↔ PushPuzzle.NCL.Strip.Sweep.Arc.Active R (t : ℤ) a := by
  have hl := scanLevel_toNat (K := K) (a.lower R)
    (endpoint_nonnegative R a.edge (a.canonical_endpoints_mem R).1)
  have hu := scanLevel_toNat (K := K) (a.upper R)
    (endpoint_nonnegative R a.edge (a.canonical_endpoints_mem R).2)
  simp only [Active, lower_ofArc, upper_ofArc, PushPuzzle.NCL.Strip.Sweep.Arc.Active]
  omega

private theorem position_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    (ofArc R a).position = (a.position R).toNat := by
  have hb := a.band R
  simp only [position, lower_ofArc, upper_ofArc, PushPuzzle.NCL.Strip.Sweep.Arc.position]
  rcases a.shape R with hs | hs
  all_goals have hy := congrArg Prod.snd hs
  all_goals dsimp only at hy
  all_goals split_ifs <;> omega

/-- The standard natural key casts to the original actual integer frontier position. -/
theorem integer_position_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) :
    ((ofArc R a).position : ℤ) = a.position R := by
  rw [position_ofArc]
  exact Int.toNat_of_nonneg (a.position_bounds R).1

private theorem toEntry_ofArc (a : PushPuzzle.NCL.Strip.Sweep.Arc R) (t : ℕ) :
    toEntry K t (ofArc R a) =
      PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.map (ofArc R) (PushPuzzle.NCL.Strip.Sweep.FrontierData.entry R (t : ℤ) a) := by
  simp only [toEntry, PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.map, PushPuzzle.NCL.Strip.Sweep.FrontierData.entry,
    active_ofArc, position_ofArc]

/-- The explicit standard-data scan returns the same actual indexed geometric frontier. -/
theorem frontier_ofFn (t : ℕ) :
    frontier K (List.ofFn R.unitRoute) t =
      (PushPuzzle.NCL.Strip.Sweep.frontier R (List.finRange m) (t : ℤ)).map (ofArc R) := by
  unfold frontier records
  rw [segments_ofFn, List.map_map, List.map_map]
  change PushPuzzle.NCL.Strip.Sweep.FrontierData.scan (2 * PushPuzzle.NCL.Strip.Sweep.height K + 1)
    ((PushPuzzle.NCL.Strip.Sweep.arcs R (List.finRange m)).map (fun a => toEntry K t (ofArc R a))) = _
  have he : ((PushPuzzle.NCL.Strip.Sweep.arcs R (List.finRange m)).map
      (fun a => toEntry K t (ofArc R a))) =
      (PushPuzzle.NCL.Strip.Sweep.FrontierData.entries R (List.finRange m) (t : ℤ)).map
        (PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.map (ofArc R)) := by
    simp only [PushPuzzle.NCL.Strip.Sweep.FrontierData.entries, List.map_map]
    apply List.map_congr_left
    intro a _
    exact toEntry_ofArc R a t
  rw [he, PushPuzzle.NCL.Strip.Sweep.FrontierData.scan_map, PushPuzzle.NCL.Strip.Sweep.FrontierData.scan_entries R (List.nodup_finRange _)]

end ArcData
end PushPuzzle.NCL.Strip.PolyTime

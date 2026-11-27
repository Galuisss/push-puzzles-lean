/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.FrontierBuckets
public import CslibFrontier.Computability.Complexity.Problems.NCL.Encoding
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat

/-!
# Standard encoded fixed-position frontier scans

An explicit candidate record contains its original label, active bit, and nonnegative geometric
key. The fixed-height bucket scan is polynomial-time under the standard record/list encoding.
Mapping the actual unit carriers to these records gives exactly the actual ordered frontier.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry`: explicit candidate label and computed geometric metadata.
* `PushPuzzle.NCL.Strip.Sweep.FrontierData.scan`: the fixed-position record scan.
* `PushPuzzle.NCL.Strip.Sweep.FrontierData.entries`: records of the actual carrier arcs at a scan cut.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.FrontierData.computableInPolyTime_scan`: standard encoded polynomial-time scan.
* `PushPuzzle.NCL.Strip.Sweep.FrontierData.scan_entries`: the scan returns the same actual ordered frontier.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep.FrontierData

open Cslib.Complexity Cslib.Complexity.NCL Cslib _root_.Turing.MultiTapeTM

/-- One original candidate label and its already computed geometric scan metadata. -/
structure Entry (Label : Type*) where
  /-- Original candidate label. -/
  label : Label
  /-- Whether the actual scan cut meets this candidate. -/
  active : Bool
  /-- Nonnegative geometric frontier position. -/
  position : ℕ

/-- Standard record encoding, with a unary geometric key and the supplied label encoding. -/
enc_structure encEntry (Label : Type) (encLabel : Label ↪ List Bool) : Entry Label where
  label : encLabel, active : encBool, position : encUnary

/-- Rename candidate labels while retaining their actual computed activity and geometric key. -/
@[expose] def Entry.map {Label Label' : Type*} (f : Label → Label') (e : Entry Label) :
    Entry Label' := ⟨f e.label, e.active, e.position⟩

/-- Filter original candidates in decreasing order of the fixed geometric keys. -/
@[expose] def scan {Label : Type*} (keyCount : ℕ) (entries : List (Entry Label)) : List Label :=
  (List.range keyCount).reverse.flatMap fun key =>
    (entries.filter (fun e => e.active && decide (e.position = key))).map PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.label

/-- The actual fixed-key scan commutes with renaming only the candidate labels. -/
theorem scan_map {Label Label' : Type*} (f : Label → Label') (keyCount : ℕ)
    (entries : List (Entry Label)) :
    scan keyCount (entries.map (PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.map f)) = (scan keyCount entries).map f := by
  simp only [scan, List.map_flatMap, List.filter_map, List.map_map, PushPuzzle.NCL.Strip.Sweep.FrontierData.Entry.map, Function.comp_def]
  rfl

/-- The actual fixed-height record scan is polynomial-time under the standard encoding. -/
theorem computableInPolyTime_scan {Label : Type} (encLabel : Label ↪ List Bool) (keyCount : ℕ) :
    ComputableInPolyTime (scan (Label := Label) keyCount)
      (encList (encEntry Label encLabel)) (encList encLabel) := by
  unfold scan
  apply ComputableInPolyTime.flatMapConst
  intro key _
  have hf : ComputableInPolyTime
      (fun entries : List (Entry Label) =>
        entries.filter (fun e => e.active && decide (e.position = key)))
      (encList (encEntry Label encLabel)) (encList (encEntry Label encLabel)) := by
    apply ComputableInPolyTime.filter
    fun_prop
  exact (ComputableInPolyTime.map (encEntry_label_polyTime Label encLabel
    ComputableInPolyTime.id')).comp hf

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Record the actual carrier-arc label, cut activity, and nonnegative geometric key. -/
@[expose] def entry (t : ℤ) (a : Arc R) : Entry (Arc R) :=
  ⟨a, decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a), (a.position R).toNat⟩

/-- Candidate records from the same explicit original-edge/unit-arc enumeration. -/
@[expose] def entries (es : List E) (t : ℤ) : List (Entry (Arc R)) :=
  (arcs R es).map (entry R t)

/-- The encoded record scan computes the same actual fixed-key carrier buckets. -/
private theorem scan_entries_eq_buckets (es : List E) (t : ℤ) :
    scan (2 * height K + 1) (entries R es t) = frontierBuckets R es t := by
  unfold scan entries frontierBuckets
  apply congrArg (List.flatMap · _)
  funext (key : ℕ)
  simp only [List.filter_map, List.map_map]
  change List.map id ((arcs R es).filter (fun a =>
    decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a) && decide ((a.position R).toNat = key))) = _
  rw [List.map_id]
  apply List.filter_congr
  intro a _
  have hb := a.position_bounds R
  simp only [← Bool.decide_and]
  apply decide_eq_decide.mpr
  exact and_congr_right (fun _ => by omega)

/-- The standard encoded scan returns exactly the same actual ordered geometric frontier. -/
theorem scan_entries {es : List E} (hes : es.Nodup) (t : ℤ) :
    scan (2 * height K + 1) (entries R es t) = frontier R es t :=
  (scan_entries_eq_buckets R es t).trans (frontierBuckets_eq R hes t)

end PushPuzzle.NCL.Strip.Sweep.FrontierData

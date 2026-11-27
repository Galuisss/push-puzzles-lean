/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Scan
public import Mathlib.Data.List.NodupEquivFin

/-!
# Actual edge creation order of the strip sweep

An actual unit arc is created when the scan visits its canonical lower endpoint. The explicit
creation stream contains each declared original carrier's unit arcs once, and no other labels.
It therefore gives a computable numbering of the exact actual unit graph edges.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.births`: actual outgoing arc labels in chronological scan order.
* `PushPuzzle.NCL.Strip.Sweep.birthEquiv`: the actual stream position as a unit-arc label.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.mem_births`: exactly the declared carriers' unit arcs are created.
* `PushPuzzle.NCL.Strip.Sweep.births_nodup`: no actual arc label is created twice.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Every actual outgoing unit-arc label, in the order in which the grid scan creates it. -/
@[expose] def births (es : List E) : List (Arc R) :=
  (List.range (scanLength R es)).flatMap
    (fun (i : ℕ) => (slice R es (scanPoint K i)).outgoing)

/-- The actual creation stream lists exactly all unit arcs of the declared original carriers. -/
theorem mem_births (es : List E) (a : Arc R) : a ∈ births R es ↔ a.edge ∈ es := by
  constructor
  · intro ha
    obtain ⟨i, _, ha⟩ := List.mem_flatMap.mp ha
    exact ((mem_slice_outgoing R es _ a).mp ha).1
  · intro he
    have hsupport := (a.canonical_endpoints_mem R).1
    have hl := (support_scan_window R a.edge hsupport).1
    have hu := support_scan_end R he hsupport
    have howner : (0 : ℤ) ≤ ownerStart R a.edge :=
      Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    let i := (level K (a.lower R)).toNat
    have hin : i < scanLength R es := by omega
    have hnonneg : 0 ≤ level K (a.lower R) := howner.trans hl
    have hpoint : scanPoint K (i : ℤ) = a.lower R := by
      rw [Int.toNat_of_nonneg hnonneg]
      exact scanPoint_level (a.band R).1
    apply List.mem_flatMap.mpr
    refine ⟨i, List.mem_range.mpr hin, ?_⟩
    exact (mem_slice_outgoing R es _ a).mpr ⟨he, hpoint.symm⟩

/-- No actual unit arc is created at two different scan sites or twice at one site. -/
theorem births_nodup {es : List E} (hes : es.Nodup) : (births R es).Nodup := by
  rw [births, List.nodup_flatMap]
  refine ⟨?_, ?_⟩
  · intro i _
    exact (frontier_nodup R hes _).filter _
  · apply List.nodup_range.imp
    intro i j hij a ha hb
    have hai := ((mem_slice_outgoing R es _ a).mp ha).2
    have haj := ((mem_slice_outgoing R es _ a).mp hb).2
    have he := congrArg (level K) (hai.symm.trans haj)
    simp only [level_scanPoint] at he
    exact hij (by exact_mod_cast he)

/-- Number the actual graph arcs by their unique actual positions in the creation stream. -/
@[expose] def birthEquiv [DecidableEq E] (es : List E) (hes : es.Nodup) (hall : ∀ e, e ∈ es) :
    Fin (births R es).length ≃ Arc R :=
  List.Nodup.getEquivOfForallMemList (births R es) (births_nodup R hes)
    (fun a => (mem_births R es a).mpr (hall a.edge))

end PushPuzzle.NCL.Strip.Sweep

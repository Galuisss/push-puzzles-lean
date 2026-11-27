/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Frontier

/-!
# Fixed-position scans of the actual strip frontier

Every geometric frontier key lies in a fixed interval determined by the strip height. Scanning
these keys in decreasing order and filtering the actual carrier arcs computes exactly the
original frontier, using only fixed finite loops and list filters.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.frontierBuckets`: actual active carrier arcs scanned by fixed geometric key.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.frontierBuckets_eq`: exact equality with the original geometric frontier.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Every actual geometric key belongs to the fixed strip-height interval. -/
theorem Arc.position_bounds (a : Arc R) : 0 ≤ a.position R ∧ a.position R ≤ 2 * height K := by
  have hb := a.band R
  rcases a.shape R with hs | hs
  · have hy := congrArg Prod.snd hs
    simp only [PushPuzzle.NCL.Strip.Sweep.Arc.position, hy, ↓reduceIte]
    omega
  · have hy := congrArg Prod.snd hs
    simp only [PushPuzzle.NCL.Strip.Sweep.Arc.position]
    split_ifs <;> omega

/-- The actual active carrier arcs, filtered once for each decreasing geometric key. -/
@[expose] def frontierBuckets (es : List E) (t : ℤ) : List (Arc R) :=
  ((List.range (2 * height K + 1)).reverse).flatMap fun (key : ℕ) =>
    (arcs R es).filter (fun a => decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a ∧ a.position R = key))

private theorem mem_bucket {es : List E} {t : ℤ} {key : ℕ} {a : Arc R} :
    a ∈ (arcs R es).filter (fun a => decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a ∧ a.position R = key)) ↔
      a.edge ∈ es ∧ PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a ∧ a.position R = key := by
  simp only [List.mem_filter, mem_arcs, decide_eq_true_eq]

private theorem mem_frontierBuckets (es : List E) (t : ℤ) (a : Arc R) :
    a ∈ frontierBuckets R es t ↔ a.edge ∈ es ∧ PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a := by
  simp only [frontierBuckets, List.mem_flatMap, List.mem_reverse, List.mem_range, mem_bucket]
  constructor
  · rintro ⟨key, _, he, ha, _⟩
    exact ⟨he, ha⟩
  · rintro ⟨he, ha⟩
    have hb := a.position_bounds R
    refine ⟨(a.position R).toNat, by omega, he, ha, ?_⟩
    omega

private theorem frontierBuckets_sorted (es : List E) (t : ℤ) :
    (frontierBuckets R es t).Pairwise (fun a b => b.position R ≤ a.position R) := by
  rw [frontierBuckets, List.pairwise_flatMap]
  constructor
  · intro key _
    apply List.pairwise_of_forall_mem_list
    intro a ha b hb
    have hka := ((mem_bucket R).mp ha).2.2
    have hkb := ((mem_bucket R).mp hb).2.2
    rw [hka, hkb]
  · apply (List.pairwise_reverse.mpr (List.pairwise_le_range (n := 2 * height K + 1))).imp
    intro key other h a ha b hb
    have hka := ((mem_bucket R).mp ha).2.2
    have hkb := ((mem_bucket R).mp hb).2.2
    rw [hka, hkb]
    exact_mod_cast h

private theorem frontierBuckets_nodup {es : List E} (hes : es.Nodup) (t : ℤ) :
    (frontierBuckets R es t).Nodup := by
  rw [frontierBuckets, List.nodup_flatMap]
  constructor
  · intro key _
    exact (arcs_nodup R hes).filter _
  · apply (List.nodup_range (n := 2 * height K + 1)).reverse.imp
    intro key other h
    apply List.disjoint_left.mpr
    intro a ha hb
    have hk := (mem_bucket R).mp ha |>.2.2
    have ho := (mem_bucket R).mp hb |>.2.2
    exact h (by omega)

/-- Fixed geometric-key scans compute the same actual ordered carrier frontier. -/
theorem frontierBuckets_eq {es : List E} (hes : es.Nodup) (t : ℤ) :
    frontierBuckets R es t = frontier R es t := by
  apply List.Perm.eq_of_pairwise (le := fun a b : Arc R => b.position R ≤ a.position R)
  · intro a b ha hb hab hba
    apply PushPuzzle.NCL.Strip.Sweep.Arc.position_injective_on R t
      ((mem_frontierBuckets R es t a).mp ha).2 ((mem_frontier R es t b).mp hb).2
    exact le_antisymm hba hab
  · exact frontierBuckets_sorted R es t
  · exact frontier_sorted R es t
  · apply (List.perm_ext_iff_of_nodup (frontierBuckets_nodup R hes t)
      (frontier_nodup R hes t)).mpr
    intro a
    rw [mem_frontierBuckets, mem_frontier]

end PushPuzzle.NCL.Strip.Sweep

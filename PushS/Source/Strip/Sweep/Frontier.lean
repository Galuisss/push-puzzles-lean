/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Arcs
import all CslibFrontier.Foundations.Geometry.Orthogonal.UnitSegments
import Mathlib.Data.List.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Linarith

/-!
# Actual bounded frontiers of the strip sweep

The scan visits lattice sites column by column, from bottom to top. A frontier is computed by
filtering the actual unit arcs at the scan cut and sorting them by their geometric height.
Every horizontal height carries at most one active arc, and at most one vertical arc is active.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.level`: the integer scan position of a lattice site.
* `PushPuzzle.NCL.Strip.Sweep.frontier`: the actual ordered unit arcs crossing a scan cut.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.frontier_length_le`: the actual frontier has at most `4 * K + 10` labels.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- The maximum ordinate of any carrier, in the original unscaled strip. -/
@[expose] def height (K : ℕ) : ℕ := 4 * K + 8

/-- Column-major scan position; all carrier ordinates lie in one block of this radix. -/
@[expose] def level (K : ℕ) (p : Point) : ℤ := (height K + 1 : ℕ) * p.1 + p.2

/-- Scan positions identify sites inside the strip's height band. -/
theorem level_injective {K : ℕ} {p q : Point}
    (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) (hq : 0 ≤ q.2 ∧ q.2 ≤ height K)
    (h : level K p = level K q) : p = q := by
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  have hd (r : Point) (hr : 0 ≤ r.2 ∧ r.2 ≤ height K) :
      level K r / (height K + 1 : ℕ) = r.1 := by
    rw [Int.ediv_eq_iff_of_pos hm]
    simp only [level, Nat.cast_add, Nat.cast_one]
    constructor <;> nlinarith
  have hx : p.1 = q.1 := by rw [← hd p hp, ← hd q hq, h]
  have hy : p.2 = q.2 := by simpa only [level, hx, add_right_inj] using h
  exact Prod.ext hx hy

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

namespace Arc

open Cslib.Complexity Cslib.Complexity.NCL

/-- Coordinatewise smaller endpoint of an actual unit arc. -/
@[expose] def lower (a : Arc R) : Point :=
  let p := (a.pair R).1
  let q := (a.pair R).2
  (min p.1 q.1, min p.2 q.2)

/-- Coordinatewise larger endpoint of an actual unit arc. -/
@[expose] def upper (a : Arc R) : Point :=
  let p := (a.pair R).1
  let q := (a.pair R).2
  (max p.1 q.1, max p.2 q.2)

/-- Every canonical arc points one unit right or one unit up. -/
theorem shape (a : Arc R) :
    a.upper R = ((a.lower R).1 + 1, (a.lower R).2) ∨
      a.upper R = ((a.lower R).1, (a.lower R).2 + 1) := by
  rcases unit_cases (a.unit R) with h | h | h | h
  all_goals simp only [lower, upper, h, Prod.mk.injEq]; omega

/-- The canonical endpoints retain the actual unit arc up to its direction. -/
theorem pair_eq (a : Arc R) :
    a.pair R = (a.lower R, a.upper R) ∨ a.pair R = (a.upper R, a.lower R) := by
  rcases unit_cases (a.unit R) with h | h | h | h
  all_goals simp only [lower, upper, h, Prod.ext_iff]; omega

/-- Both canonical endpoints belong to the complete original carrier support. -/
theorem canonical_endpoints_mem (a : Arc R) :
    realPoint (a.lower R) ∈ support (R.route a.edge) ∧
      realPoint (a.upper R) ∈ support (R.route a.edge) := by
  have hm := a.endpoints_mem R
  rcases a.pair_eq R with h | h
  · simpa only [h] using hm
  · simpa only [h] using hm.symm

/-- Canonical geometric endpoints identify the original unit-arc label. -/
private theorem eq_of_endpoints {a b : Arc R} (hl : a.lower R = b.lower R)
    (hu : a.upper R = b.upper R) : a = b := by
  apply undirected_injective R
  rcases a.pair_eq R with ha | ha <;> rcases b.pair_eq R with hb | hb
  all_goals simp only [ha, hb, hl, hu, or_true, true_or]

/-- Both canonical endpoints lie inside the carrier height band. -/
theorem band (a : Arc R) :
    (0 ≤ (a.lower R).2 ∧ (a.lower R).2 ≤ height K) ∧
      (0 ≤ (a.upper R).2 ∧ (a.upper R).2 ≤ height K) := by
  have he := a.endpoints_mem R
  have hp := (R.support_window a.edge he.1).2.2
  have hq := (R.support_window a.edge he.2).2.2
  simp only [realPoint] at hp hq
  have hp' : 4 ≤ (a.pair R).1.2 ∧ (a.pair R).1.2 ≤ 4 * (K : ℤ) + 8 := by
    exact_mod_cast hp
  have hq' : 4 ≤ (a.pair R).2.2 ∧ (a.pair R).2.2 ≤ 4 * (K : ℤ) + 8 := by
    exact_mod_cast hq
  simp only [lower, upper, height, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  omega

/-- Whether the original traversal of this unit arc runs against the canonical sweep direction. -/
@[expose] def reversed (a : Arc R) : Bool := decide ((a.pair R).1 = a.upper R)

/-- The scan passes the lower endpoint strictly before the upper endpoint. -/
theorem level_lt (a : Arc R) : level K (a.lower R) < level K (a.upper R) := by
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  rcases a.shape R with h | h
  all_goals simp only [level, h]; nlinarith

/-- The canonical endpoint selected by an incidence direction. -/
@[expose] def endpoint (a : Arc R) (d : Bool) : Point := if d then a.upper R else a.lower R

/-- Rebasing either traversal endpoint gives its canonical upper/lower incidence bit. -/
theorem direction_at (a : Arc R) (d : Bool) :
    (a.reversed R ^^ d) = decide ((if d then (a.pair R).2 else (a.pair R).1) = a.upper R) := by
  have hne : a.lower R ≠ a.upper R := by
    intro h
    have ht := a.level_lt R
    rw [h] at ht
    exact (lt_self_iff_false _).mp ht
  cases d
  · simp [reversed]
  · rcases a.pair_eq R with h | h
    all_goals simp [reversed, h, hne]

/-- An arc crosses the cut immediately before scan position `t`. -/
@[expose] def Active (t : ℤ) (a : Arc R) : Prop :=
  level K (a.lower R) < t ∧ t ≤ level K (a.upper R)

instance (t : ℤ) (a : Arc R) : Decidable (Active R t a) := inferInstanceAs (Decidable (_ ∧ _))

/-- Height key for the geometric frontier order; the vertical arc lies between adjacent rows. -/
@[expose] def position (a : Arc R) : ℤ :=
  if (a.lower R).2 = (a.upper R).2 then 2 * (a.lower R).2 else 2 * (a.upper R).2 - 1

/-- A finite lane used to count the actual frontier: horizontal height or the unique vertical arc.
-/
@[expose] def lane (a : Arc R) : Fin (height K + 2) :=
  if (a.lower R).2 = (a.upper R).2 then
    ⟨(a.lower R).2.toNat, by have hb := (a.band R).1; omega⟩
  else ⟨height K + 1, by omega⟩

private theorem horizontal_left (t : ℤ) (a : Arc R) (ha : Active R t a)
    (hh : (a.lower R).2 = (a.upper R).2) :
    (t - (a.lower R).2 - 1) / (height K + 1 : ℕ) = (a.lower R).1 := by
  have hs : a.upper R = ((a.lower R).1 + 1, (a.lower R).2) := by
    rcases a.shape R with h | h
    · exact h
    · have := congrArg Prod.snd h; omega
  rw [Int.ediv_eq_iff_of_pos (by omega)]
  simp only [Active, level, hs] at ha
  constructor <;> nlinarith [ha.1, ha.2]

private theorem vertical_top (t : ℤ) (a : Arc R) (ha : Active R t a)
    (hh : (a.lower R).2 ≠ (a.upper R).2) : level K (a.upper R) = t := by
  have hs : a.upper R = ((a.lower R).1, (a.lower R).2 + 1) := by
    rcases a.shape R with h | h
    · exact False.elim (hh (congrArg Prod.snd h).symm)
    · exact h
  simp only [Active, level, hs] at ha ⊢
  omega

/-- The actual active frontier uses each finite lane at most once. -/
private theorem lane_injective_on (t : ℤ) {a b : Arc R} (ha : Active R t a) (hb : Active R t b)
    (h : a.lane R = b.lane R) : a = b := by
  by_cases hha : (a.lower R).2 = (a.upper R).2 <;>
    by_cases hhb : (b.lower R).2 = (b.upper R).2
  · have hy : (a.lower R).2 = (b.lower R).2 := by
      have hv := congrArg Fin.val h
      simp only [lane, hha, hhb, ↓reduceIte] at hv
      have hab := a.band R; have hbb := b.band R
      omega
    have hx : (a.lower R).1 = (b.lower R).1 := by
      rw [← horizontal_left R t a ha hha, ← horizontal_left R t b hb hhb, hy]
    have hl := Prod.ext hx hy
    apply eq_of_endpoints R hl
    have hsa := (a.shape R).resolve_right (fun h => by
      have := congrArg Prod.snd h
      omega)
    have hsb := (b.shape R).resolve_right (fun h => by
      have := congrArg Prod.snd h
      omega)
    simp only [hsa, hsb, hl]
  · have hv := congrArg Fin.val h
    simp only [lane, hha, hhb, ↓reduceIte] at hv
    have hab := a.band R
    omega
  · have hv := congrArg Fin.val h
    simp only [lane, hha, hhb, ↓reduceIte] at hv
    have hbb := b.band R
    omega
  · have hu := level_injective (a.band R).2 (b.band R).2
      ((vertical_top R t a ha hha).trans (vertical_top R t b hb hhb).symm)
    apply eq_of_endpoints R ?_ hu
    have hsa := (a.shape R).resolve_left (fun h => hha (congrArg Prod.snd h).symm)
    have hsb := (b.shape R).resolve_left (fun h => hhb (congrArg Prod.snd h).symm)
    have hx := congrArg Prod.fst hu
    have hy := congrArg Prod.snd hu
    rw [hsa, hsb] at hx hy
    apply Prod.ext <;> dsimp only at hx hy ⊢ <;> omega

/-- Geometric frontier positions distinguish all actual active unit arcs. -/
theorem position_injective_on (t : ℤ) {a b : Arc R} (ha : Active R t a) (hb : Active R t b)
    (h : a.position R = b.position R) : a = b := by
  apply lane_injective_on R t ha hb
  by_cases hha : (a.lower R).2 = (a.upper R).2 <;>
    by_cases hhb : (b.lower R).2 = (b.upper R).2
  · have hy : (a.lower R).2 = (b.lower R).2 := by
      simp only [position, hha, hhb, ↓reduceIte] at h
      omega
    apply Fin.ext
    simpa only [lane, hha, hhb, ↓reduceIte] using congrArg Int.toNat hy
  · simp only [position, hha, hhb, ↓reduceIte] at h
    omega
  · simp only [position, hha, hhb, ↓reduceIte] at h
    omega
  · simp only [lane, hha, hhb, ↓reduceIte]

end Arc

/-- Actual frontier labels, in decreasing geometric height order. -/
@[expose] def frontier (es : List E) (t : ℤ) : List (Arc R) :=
  ((arcs R es).filter (fun a => decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a))).mergeSort
    (fun a b => decide (b.position R ≤ a.position R))

/-- The computed frontier contains exactly the declared unit arcs crossing its cut. -/
theorem mem_frontier (es : List E) (t : ℤ) (a : Arc R) :
    a ∈ frontier R es t ↔ a.edge ∈ es ∧ PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a := by
  unfold frontier
  rw [(List.mergeSort_perm _ _).mem_iff]
  simp only [List.mem_filter, mem_arcs, decide_eq_true_eq]

/-- Sorting the actual active arcs preserves their distinct labels. -/
theorem frontier_nodup {es : List E} (hes : es.Nodup) (t : ℤ) :
    (frontier R es t).Nodup :=
  (List.mergeSort_perm _ _).nodup_iff.mpr ((arcs_nodup R hes).filter _)

/-- Actual frontier labels are sorted from higher to lower geometric position. -/
theorem frontier_sorted (es : List E) (t : ℤ) :
    (frontier R es t).Pairwise (fun a b => b.position R ≤ a.position R) := by
  have hs := List.pairwise_mergeSort
    (le := fun a b : Arc R => decide (b.position R ≤ a.position R))
    (fun a b c hab hbc => by
      simp only [decide_eq_true_eq] at hab hbc ⊢
      exact hbc.trans hab)
    (fun a b => by
      simp only [Bool.or_eq_true, decide_eq_true_eq]
      exact le_total _ _) ((arcs R es).filter (fun a => decide (PushPuzzle.NCL.Strip.Sweep.Arc.Active R t a)))
  simpa only [frontier, decide_eq_true_eq] using hs

/-- The actual frontier width depends only on the fixed strip height. -/
theorem frontier_length_le {es : List E} (hes : es.Nodup) (t : ℤ) :
    (frontier R es t).length ≤ 4 * K + 10 := by
  have hn : ((frontier R es t).map (PushPuzzle.NCL.Strip.Sweep.Arc.lane R)).Nodup := by
    apply (frontier_nodup R hes t).map_on
    intro a ha b hb hab
    exact PushPuzzle.NCL.Strip.Sweep.Arc.lane_injective_on R t ((mem_frontier R es t a).mp ha).2
      ((mem_frontier R es t b).mp hb).2 hab
  have hc := hn.length_le_card
  rw [List.length_map] at hc
  simpa only [Fintype.card_fin, height, Nat.add_assoc, Nat.reduceAdd] using hc

end PushPuzzle.NCL.Strip.Sweep

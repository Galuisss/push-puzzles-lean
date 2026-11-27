/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.Source.Strip.Sweep.Wires
import Mathlib.Tactic.Linarith

/-!
# Consecutive actual grid scan steps

Integer division enumerates the strip column by column. Each computed slice connects the actual
frontier at `t` to the actual frontier at `t+1`. Complete carrier support lies in a fixed-size
interval of scan positions relative to its owner panel.

## Main definitions

* `PushPuzzle.NCL.Strip.Sweep.scanPoint`: the grid site at an integer scan position.
* `PushPuzzle.NCL.Strip.Sweep.scan`: the explicit finite list of actual local slices.
* `PushPuzzle.NCL.Strip.Sweep.scanSpan`: a uniform scan-position budget for one complete carrier.

## Main results

* `PushPuzzle.NCL.Strip.Sweep.scan_before`, `PushPuzzle.NCL.Strip.Sweep.scan_after`: actual consecutive frontier matching.
* `PushPuzzle.NCL.Strip.Sweep.support_scan_window`: the complete carrier's scan-position interval.
-/

public section

namespace PushPuzzle.NCL.Strip.Sweep

open Cslib.Complexity Cslib.Complexity.NCL Cslib Cslib.Orthogonal

/-- Decode a column-major integer position into its actual strip grid site. -/
@[expose] def scanPoint (K : ℕ) (t : ℤ) : Point :=
  (t / (height K + 1 : ℕ), t % (height K + 1 : ℕ))

/-- Every scan site is in the fixed height band. -/
theorem scanPoint_band (K : ℕ) (t : ℤ) :
    0 ≤ (scanPoint K t).2 ∧ (scanPoint K t).2 ≤ height K := by
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  have hl := Int.emod_nonneg t (ne_of_gt hm)
  have hu := Int.emod_lt_of_pos t hm
  simp only [scanPoint]
  omega

/-- The decoded site is exactly the next grid site of the actual scan. -/
theorem level_scanPoint (K : ℕ) (t : ℤ) : level K (scanPoint K t) = t := by
  simp only [level, scanPoint]
  exact Int.mul_ediv_add_emod t _

/-- Decoding the scan position of any actual strip site recovers that exact grid site. -/
theorem scanPoint_level {K : ℕ} {p : Point} (hp : 0 ≤ p.2 ∧ p.2 ≤ height K) :
    scanPoint K (level K p) = p :=
  level_injective (scanPoint_band K _) hp (level_scanPoint K _)

variable {V E : Type*} {A K : ℕ} (R : Environment V E A K)

/-- Actual local slices at consecutive scan positions, starting with zero. -/
@[expose] def scan (es : List E) (n : ℕ) : List (Slice R) :=
  List.ofFn (fun i : Fin n => slice R es (scanPoint K i.val))

/-- The actual preceding frontier is the computed slice's incoming interface and context. -/
theorem scan_before (es : List E) (t : ℤ) :
    frontier R es t =
      (slice R es (scanPoint K t)).above ++ (slice R es (scanPoint K t)).incoming ++
        (slice R es (scanPoint K t)).below := by
  simpa only [level_scanPoint] using slice_before R es (scanPoint_band K t)

/-- The actual following frontier is the computed slice's outgoing interface and context. -/
theorem scan_after {es : List E} (hes : es.Nodup) (t : ℤ) :
    frontier R es (t + 1) =
      (slice R es (scanPoint K t)).above ++ (slice R es (scanPoint K t)).outgoing ++
        (slice R es (scanPoint K t)).below := by
  simpa only [level_scanPoint] using slice_after R hes (scanPoint_band K t)

/-- Uniform scan-position span of every complete carrier, depending only on strip capacities. -/
@[expose] def scanSpan (A K : ℕ) : ℕ := (16 * A + 1) * (height K + 1)

/-- The scan position at the left edge of an owner's panel. -/
@[expose] def ownerStart (e : E) : ℤ := (height K + 1 : ℕ) * (8 * A * R.edges.row e : ℕ)

/-- Every grid point of the complete continuous carrier lies in its owner's fixed scan interval.
-/
theorem support_scan_window (e : E) {p : Point} (hp : realPoint p ∈ support (R.route e)) :
    ownerStart R e ≤ level K p ∧ level K p < ownerStart R e + scanSpan A K := by
  have h := R.support_window e hp
  have hx : 8 * (A : ℤ) * R.edges.row e + 2 ≤ p.1 ∧
      p.1 ≤ 8 * (A : ℤ) * (R.edges.row e + 2) - 2 := by
    have hx := And.intro h.1 h.2.1
    simp only [realPoint] at hx
    exact_mod_cast hx
  have hy : 4 ≤ p.2 ∧ p.2 ≤ (height K : ℤ) := by
    have hy := h.2.2
    simp only [realPoint] at hy
    exact_mod_cast hy
  have hm : (0 : ℤ) < (height K + 1 : ℕ) := by omega
  have hl := Int.mul_le_mul_of_nonneg_left hx.1 (Int.le_of_lt hm)
  have hu := Int.mul_le_mul_of_nonneg_left hx.2 (Int.le_of_lt hm)
  simp only [level, ownerStart, scanSpan, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  constructor <;> nlinarith

/-- End position after all complete carriers in the explicit edge list. -/
@[expose] def scanLength (es : List E) : ℕ :=
  (8 * A * ((es.map R.edges.row).foldr max 0 + 2) + 1) * (height K + 1)

private theorem owner_le {es : List E} {e : E} (he : e ∈ es) :
    R.edges.row e ≤ (es.map R.edges.row).foldr max 0 := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons f es ih =>
    rcases List.mem_cons.mp he with he | he
    · subst f
      exact Nat.le_max_left _ _
    · exact (ih he).trans (Nat.le_max_right _ _)

private theorem owner_end_le {es : List E} {e : E} (he : e ∈ es) :
    ownerStart R e + scanSpan A K ≤ scanLength R es := by
  have hr : (R.edges.row e : ℤ) ≤ (es.map R.edges.row).foldr max 0 := by
    exact_mod_cast owner_le R he
  have h₀ := Int.mul_le_mul_of_nonneg_left hr (show (0 : ℤ) ≤ 8 * A by omega)
  have h₁ := Int.mul_le_mul_of_nonneg_left h₀
    (show (0 : ℤ) ≤ (height K + 1 : ℕ) by omega)
  simp only [ownerStart, scanSpan, scanLength, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  nlinarith

/-- Every declared complete carrier is finished strictly before the computed end of the scan. -/
theorem support_scan_end {es : List E} {e : E} (he : e ∈ es) {p : Point}
    (hp : realPoint p ∈ support (R.route e)) : level K p < scanLength R es :=
  ((support_scan_window R e hp).2).trans_le (owner_end_le R he)

/-- Before the first grid site, the actual carrier frontier is empty. -/
theorem frontier_zero (es : List E) : frontier R es 0 = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  have hactive := ((mem_frontier R es 0 a).mp ha).2
  have hw := (support_scan_window R a.edge (a.canonical_endpoints_mem R).1).1
  have hn : (0 : ℤ) ≤ ownerStart R a.edge :=
    Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hl := hactive.1
  omega

/-- After the explicit scan length, every actual carrier frontier has closed. -/
theorem frontier_scanLength (es : List E) : frontier R es (scanLength R es) = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro a ha
  obtain ⟨he, hactive⟩ := (mem_frontier R es _ a).mp ha
  have hw := (support_scan_window R a.edge (a.canonical_endpoints_mem R).2).2
  have hend := owner_end_le R he
  have hu := hactive.2
  omega

end PushPuzzle.NCL.Strip.Sweep

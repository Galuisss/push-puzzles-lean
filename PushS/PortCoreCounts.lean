/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortEndpointSeparation
import all PushS.PortEndpointCounts
import all PushS.PortEndpointSeparation
import all PushS.PortSegments

/-!
# Inventories and fixed-hole separation of the actual three-port core

The three emitted core segments retain their original signal order. Their horizontal
traces combine with the actual outer endpoint traces to give κ+11 holes; their middle
axis combines with its upper endpoint to give four. Native coordinate reads also
separate the core signals from its actual fixed streets, branches and markers.

## Main results

* `gateHorizontals_card`: the complete horizontal-track inventory is κ+11.
* `gateMiddleAxis_card`: the complete middle-axis inventory is four.
* `gateFixedSegments_disjoint`: same-core fixed/signal separation.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

/-- The actual G/J horizontal gaps satisfy the left/right physical-bit inventory identity. -/
theorem gateSegments_horizontal_card (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    (pointHoles ((gateSegments (coordinates p) state kind first internal).take 2)).card +
      (state.internal.getD internal false).toNat = kind.kappa.toNat + 8 +
        (state.internal.getD (internal + 2) false).toNat := by
  let x := (coordinates p).x (first + 1)
  let y := onSide (coordinates p) .lower ((coordinates p).depth 1)
  let l := (state.internal.getD internal false).toNat
  let r := (state.internal.getD (internal + 2) false).toNat
  let t := if state.internal.getD (internal + 1) false then 6 else 1
  let k := kind.kappa.toNat
  let g := segment (x + 2 + l - k) y (x + t) y
  let j := segment (x + t + 3) y (x + 11 + r) y
  have hx : 64 < x := by
    have h := readLength_add_lt_x p (first + 1) 0
    change 64 < p.x (first + 1)
    omega
  have hl : l ≤ 1 := Bool.toNat_le _
  have hr : r ≤ 1 := Bool.toNat_le _
  have ht : 1 ≤ t ∧ t ≤ 6 := by dsimp only [t]; split <;> decide +kernel
  have hk : 2 ≤ k ∧ k ≤ 4 := by cases kind <;> decide +kernel
  have hd : Disjoint (pointHoles [g]) (pointHoles [j]) := by
    apply Finset.disjoint_left.mpr
    intro q hqg hqj
    have hg := (horizontal_mem (x + 2 + l - k) (x + t) y q).mp hqg
    have hj := (horizontal_mem (x + t + 3) (x + 11 + r) y q).mp hqj
    omega
  change (pointHoles ([g] ++ [j])).card + l = k + 8 + r
  rw [pointHoles_append, Finset.card_union_of_disjoint hd]
  dsimp only [g, j]
  rw [horizontal_card, horizontal_card]
  omega

/-- The actual lower middle-axis trace has two holes minus its physical axis bit. -/
theorem gateSegments_axis_card (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    (pointHoles ((gateSegments (coordinates p) state kind first internal).drop 2)).card +
      (state.axes.getD (first + 1) false).toNat = 2 := by
  have hu : 16384 ≤ (coordinates p).depth 1 := readDepth_ge p (by omega) p.levels_pos
  have hh : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
  dsimp only [gateSegments]
  simp only [List.drop_succ_cons, List.drop_zero]
  rw [vertical_card]
  simp [onSide, coordinates] at hu hh hb ⊢
  omega

/-- The actual horizontal gaps and middle-axis trace have no common hole. -/
theorem gateSegments_parts_disjoint (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    Disjoint (pointHoles ((gateSegments (coordinates p) state kind first internal).take 2))
      (pointHoles ((gateSegments (coordinates p) state kind first internal).drop 2)) := by
  have hu : 16384 ≤ (coordinates p).depth 1 := readDepth_ge p (by omega) p.levels_pos
  have hh : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
  apply Finset.disjoint_left.mpr
  intro q hhorizontal haxis
  dsimp only [gateSegments] at hhorizontal haxis
  simp only [List.take_succ_cons, List.take_zero,
    mem_pointHoles, List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at hhorizontal
  simp only [List.drop_succ_cons, List.drop_zero] at haxis
  have hv := (vertical_mem _ _ _ q).mp haxis
  have hy : q.2 = onSide (coordinates p) .lower ((coordinates p).depth 1) := by
    rcases hhorizontal with hq | hq
    · exact (horizontal_coordinates hq).1
    · exact (horizontal_coordinates hq).1
  rw [hy] at hv
  simp [onSide, coordinates] at hu hh hb hv
  omega

/-- Exact inventory identity for the actual three core signal segments. -/
theorem gateSegments_card (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    (pointHoles (gateSegments (coordinates p) state kind first internal)).card +
      (state.internal.getD internal false).toNat +
      (state.axes.getD (first + 1) false).toNat = kind.kappa.toNat + 10 +
        (state.internal.getD (internal + 2) false).toNat := by
  have hh := gateSegments_horizontal_card p state kind first internal
  have hv := gateSegments_axis_card p state kind first internal
  rw [← List.take_append_drop 2 (gateSegments (coordinates p) state kind first internal), pointHoles_append,
    Finset.card_union_of_disjoint (gateSegments_parts_disjoint p state kind first internal)]
  omega

/-- The actual G/J gaps stay within twelve cells of their actual middle axis. -/
theorem gateSegments_horizontal_span (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((gateSegments (coordinates p) state kind first internal).take 2)) :
    p.x (first + 1) - 2 ≤ q.1 ∧ q.1 ≤ p.x (first + 1) + 12 := by
  have hx := readLength_add_lt_x p (first + 1) 0
  have hl := Bool.toNat_le (state.internal.getD internal false)
  have hr := Bool.toNat_le (state.internal.getD (internal + 2) false)
  have ht : (if state.internal.getD (internal + 1) false then 6 else 1) ≤ (6 : ℕ) := by
    split <;> decide +kernel
  have hk : 2 ≤ kappaNat kind ∧ kappaNat kind ≤ 4 := by cases kind <;> decide +kernel
  dsimp only [gateSegments] at hq
  simp only [List.take_succ_cons, List.take_zero, mem_pointHoles,
    List.mem_cons, List.not_mem_nil, or_false, exists_eq_or_imp, exists_eq_left] at hq
  change readLength p 0 + 64 < (coordinates p).x (first + 1) at hx
  change (coordinates p).x (first + 1) - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x (first + 1) + 12
  rcases hq with hq | hq
  all_goals have hh := horizontal_coordinates hq
  all_goals omega

private theorem gate_outer_disjoint (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    Disjoint (pointHoles ((endpointSegments (coordinates p) state
      ⟨.lower, first, true, 1, internal⟩).drop 1 ++
      (endpointSegments (coordinates p) state
        ⟨.lower, first + 2, false, 1, internal + 2⟩).drop 1))
      (pointHoles ((gateSegments (coordinates p) state kind first internal).take 2)) := by
  let left : Endpoint := ⟨.lower, first, true, 1, internal⟩
  let right : Endpoint := ⟨.lower, first + 2, false, 1, internal + 2⟩
  rw [pointHoles_append]
  apply Finset.disjoint_left.mpr
  intro q hq hc
  have hcs := gateSegments_horizontal_span p state kind first internal hc
  rcases Finset.mem_union.mp hq with hq | hq
  · have hl := horizontal_span p state left hq
    have hsep := axes_separated p (show first < first + 1 by omega)
    change p.x first - 2 ≤ q.1 ∧ q.1 ≤ p.x first + 2 at hl
    omega
  · have hr := horizontal_span p state right hq
    have hsep := axes_separated p (show first + 1 < first + 2 by omega)
    change p.x (first + 2) - 2 ≤ q.1 ∧ q.1 ≤ p.x (first + 2) + 2 at hr
    omega

/-- The two actual external horizontal-near traces and G/J gaps contain exactly κ+11 holes. -/
theorem gateHorizontals_card (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    (pointHoles ((endpointSegments (coordinates p) state
        ⟨.lower, first, true, 1, internal⟩).drop 1 ++
      (endpointSegments (coordinates p) state
        ⟨.lower, first + 2, false, 1, internal + 2⟩).drop 1 ++
      (gateSegments (coordinates p) state kind first internal).take 2)).card = kind.kappa.toNat + 11 := by
  let left : Endpoint := ⟨.lower, first, true, 1, internal⟩
  let right : Endpoint := ⟨.lower, first + 2, false, 1, internal + 2⟩
  let ls := (endpointSegments (coordinates p) state left).drop 1
  let rs := (endpointSegments (coordinates p) state right).drop 1
  let cs := (gateSegments (coordinates p) state kind first internal).take 2
  have hleft := endpointSegments_horizontal_card p state left
  have hright := endpointSegments_horizontal_card p state right
  have hcore := gateSegments_horizontal_card p state kind first internal
  have hwire : Disjoint (pointHoles ls) (pointHoles rs) :=
    endpointHorizontals_disjoint p state left right (by dsimp [left, right]; omega)
  have hdis : Disjoint (pointHoles (ls ++ rs)) (pointHoles cs) :=
    gate_outer_disjoint p state kind first internal
  change (pointHoles ((ls ++ rs) ++ cs)).card = _
  rw [pointHoles_append, Finset.card_union_of_disjoint hdis, pointHoles_append,
    Finset.card_union_of_disjoint hwire]
  change (pointHoles ls).card = 1 + (state.internal.getD internal false).toNat at hleft
  change (pointHoles rs).card = 1 + (!(state.internal.getD (internal + 2) false)).toNat at hright
  change (pointHoles cs).card + (state.internal.getD internal false).toNat =
    kind.kappa.toNat + 8 + (state.internal.getD (internal + 2) false).toNat at hcore
  have hnot : (state.internal.getD (internal + 2) false).toNat +
      (!(state.internal.getD (internal + 2) false)).toNat = 1 := by
    cases state.internal.getD (internal + 2) false <;> decide +kernel
  omega

private theorem core_axis_lower (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles ((gateSegments (coordinates p) state kind first internal).drop 2)) : p.D < q.2 := by
  have hu : (coordinates p).depth 1 + 64 < p.D := readDepth_add_lt_D p 1
  have hH : p.H = 2 * p.D := rfl
  have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
  dsimp only [gateSegments] at hq
  simp only [List.drop_succ_cons, List.drop_zero] at hq
  have hv := (vertical_mem _ _ _ q).mp hq
  simp [onSide, coordinates] at hu hb hv
  omega

/-- The actual upper middle-axis trace and lower core-axis trace contain exactly four holes. -/
theorem gateMiddleAxis_card (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) (upper : Endpoint)
    (hs : upper.side = .upper) (hp : upper.port = first + 1)
    (hj : 1 ≤ upper.level) (hm : upper.level ≤ p.levels) :
    (pointHoles ((endpointSegments (coordinates p) state upper).take 1 ++
      (gateSegments (coordinates p) state kind first internal).drop 2)).card = 4 := by
  have hu := endpointSegments_axis_card p state upper hj hm
  have hc := gateSegments_axis_card p state kind first internal
  have hd : Disjoint (pointHoles ((endpointSegments (coordinates p) state upper).take 1))
      (pointHoles ((gateSegments (coordinates p) state kind first internal).drop 2)) := by
    apply Finset.disjoint_left.mpr
    intro q hqu hqc
    have hupper := upper_axis_row p state upper hs hqu
    have hlower := core_axis_lower p state kind first internal hqc
    omega
  rw [pointHoles_append, Finset.card_union_of_disjoint hd]
  simp only [hs, hp, ite_true] at hu
  omega

/-- Every actual core signal hole lies on the working row or its middle-axis near trace. -/
theorem gateSegments_working_band (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) {q : ℕ × ℕ}
    (hq : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) :
    p.H - (readDepth p 1 + 2) ≤ q.2 ∧
      q.2 ≤ p.H - readDepth p 1 ∧
      (q.2 = p.H - readDepth p 1 ∨ q.1 = p.x (first + 1)) := by
  change p.H - ((coordinates p).depth 1 + 2) ≤ q.2 ∧
    q.2 ≤ p.H - (coordinates p).depth 1 ∧
    (q.2 = p.H - (coordinates p).depth 1 ∨ q.1 = (coordinates p).x (first + 1))
  have hu : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  have hb := Bool.toNat_le (state.axes.getD (first + 1) false)
  rw [← List.take_append_drop 2 (gateSegments (coordinates p) state kind first internal), pointHoles_append,
    Finset.mem_union] at hq
  dsimp only [gateSegments] at hq
  simp only [List.take_succ_cons, List.take_zero, List.drop_succ_cons,
    List.drop_zero, mem_pointHoles, List.mem_cons, List.not_mem_nil, or_false,
    exists_eq_or_imp, exists_eq_left] at hq
  have hside : Side.lower ≠ .upper := by decide
  rcases hq with (hq | hq) | hq
  · have hh := horizontal_coordinates hq
    simp only [onSide, hside, ite_false, coordinates] at hh
    simp only [coordinates] at hu ⊢
    exact ⟨by omega, by omega, Or.inl hh.1⟩
  · have hh := horizontal_coordinates hq
    simp only [onSide, hside, ite_false, coordinates] at hh
    simp only [coordinates] at hu ⊢
    exact ⟨by omega, by omega, Or.inl hh.1⟩
  · have hv := vertical_coordinates hq
    simp only [onSide, hside, ite_false, coordinates] at hu hb hv ⊢
    exact ⟨by omega, by omega, Or.inr hv.1⟩

private theorem gate_fixed_no_contact (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ)
    {q : ℕ × ℕ} (hfixed : q ∈ pointHoles (gateFixedSegments (coordinates p) (first + 1)))
    (hsignal : q ∈ pointHoles (gateSegments (coordinates p) state kind first internal)) : False := by
  have hnear := gateSegments_working_band p state kind first internal hsignal
  change p.H - ((coordinates p).depth 1 + 2) ≤ q.2 ∧
    q.2 ≤ p.H - (coordinates p).depth 1 ∧
    (q.2 = p.H - (coordinates p).depth 1 ∨ q.1 = (coordinates p).x (first + 1)) at hnear
  have hu : 16384 ≤ (coordinates p).depth 1 := readDepth_ge p (by omega) p.levels_pos
  have huH : (coordinates p).depth 1 + 64 < p.H := readDepth_add_lt_H p 1
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
  dsimp only [gateFixedSegments] at hs
  simp only [List.mem_append, or_assoc] at hs
  have hside : Side.lower ≠ .upper := by decide
  rcases hs with hs | hs | hs
  · obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs
    have hv := vertical_coordinates hq
    simp only [onSide, hside, ite_false, coordinates] at hv
    change 16384 ≤ _ at hu
    simp only [coordinates] at hnear hu huH
    omega
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl
    · have hp := point_coordinates hq
      simp only [onSide, hside, ite_false, coordinates] at hp
      simp only [coordinates] at hnear hu huH
      omega
    · have hh := horizontal_coordinates hq
      simp only [onSide, hside, ite_false, coordinates] at hh
      simp only [coordinates] at hnear hu huH
      omega
    · have hp := point_coordinates hq
      simp only [onSide, hside, ite_false, coordinates] at hp
      simp only [coordinates] at hnear hu huH
      omega
    · have hp := point_coordinates hq
      simp only [onSide, hside, ite_false, coordinates] at hp
      simp only [coordinates] at hnear hu huH
      omega
  · split at hs
    · have hM : 1 < p.levels := by assumption
      have hn : (coordinates p).depth 2 + 64 < p.H := readDepth_add_lt_H p 2
      have hg := readDepth_interlevel_margin p (by omega : 1 ≤ 1) hM
      change 2 * p.b 1 + 6 < ((coordinates p).depth 2 - (coordinates p).depth 1) / 2 - 2 at hg
      obtain ⟨col, _, rfl⟩ := List.mem_map.mp hs
      have hp := point_coordinates hq
      simp only [onSide, hside, ite_false, coordinates] at hp
      simp only [coordinates] at hnear hu huH hn hg
      omega
    · cases hs

/-- The actual core's fixed streets, branches, half-depth and interlevel markers share no
hole with its actual three signal segments. -/
theorem gateFixedSegments_disjoint (p : Scales.Parameters) (state : SignalState)
    (kind : Shuttle.Kind) (first internal : ℕ) :
    Disjoint (pointHoles (gateFixedSegments (coordinates p) (first + 1)))
      (pointHoles (gateSegments (coordinates p) state kind first internal)) :=
  Finset.disjoint_left.mpr fun _ hf hs => gate_fixed_no_contact p state kind first internal hf hs

end PushPuzzle.PushS.PortLayout

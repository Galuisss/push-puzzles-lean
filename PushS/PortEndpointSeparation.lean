/-
Copyright (c) 2026 Xuyang Peng. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xuyang Peng
-/

module

public import PushS.PortSignalSeparation
import all PushS.PortEndpointCounts
import all PushS.PortSegments

/-!
# Separation of an actual endpoint's fixed and signal holes

The f street and long branch lie outward from its axis-near and inward signal holes.
The r street ends before the working row; its later marker lies beyond that row.
-/

public section

namespace PushPuzzle.PushS.PortLayout


open PushFS.Reduction SegmentRecipe

attribute [local simp] inward outward auxiliary

private theorem endpoint_near (p : Scales.Parameters) (state : SignalState) (e : Endpoint)
    {q : ℕ × ℕ} (hq : q ∈ pointHoles (endpointSegments (coordinates p) state e)) :
    (if e.inward then (coordinates p).x e.port ≤ q.1 ∧ q.1 ≤ (coordinates p).x e.port + 2
      else (coordinates p).x e.port - 2 ≤ q.1 ∧ q.1 ≤ (coordinates p).x e.port) ∧
    (q.1 = (coordinates p).x e.port ∨
      q.2 = onSide (coordinates p) e.side ((coordinates p).depth e.level)) := by
  rw [← List.take_append_drop 1 (endpointSegments (coordinates p) state e),
    pointHoles_append, Finset.mem_union] at hq
  rcases hq with hq | hq
  · have h := (axis_mem p state e q).mp hq
    change q.1 = (coordinates p).x e.port ∧ _ at h
    constructor
    · cases hd : e.inward <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega
    · exact Or.inl h.1
  · have hx : 64 < (coordinates p).x e.port := by
      have h := readLength_add_lt_x p e.port 0
      change 64 < p.x e.port
      omega
    have hbit := Bool.toNat_le (if e.inward then state.internal.getD e.internal false
      else !(state.internal.getD e.internal false))
    dsimp only [endpointSegments] at hq
    simp only [List.drop_succ_cons, List.drop_zero, horizontal_mem] at hq
    constructor
    · cases hd : e.inward <;> simp [hd] at hq hbit ⊢ <;> omega
    · exact Or.inr hq.1

private theorem rows_injective (p : Scales.Parameters) (side : Side) {u v : ℕ}
    (hu : u ≤ p.H) (hv : v ≤ p.H)
    (he : onSide (coordinates p) side u = onSide (coordinates p) side v) : u = v := by
  cases side <;> simp [onSide, coordinates] at he <;> omega

private theorem row_between (p : Scales.Parameters) (side : Side) {a b u : ℕ}
    (ha : a ≤ p.H) (hb : b ≤ p.H) (hu : u ≤ p.H)
    (hlo : min (onSide (coordinates p) side a) (onSide (coordinates p) side b) ≤
      onSide (coordinates p) side u)
    (hhi : onSide (coordinates p) side u ≤
      max (onSide (coordinates p) side a) (onSide (coordinates p) side b)) :
    min a b ≤ u ∧ u ≤ max a b := by
  cases side <;> simp [onSide, coordinates] at hlo hhi <;> omega

private theorem vertical_coordinates {x y v : ℕ} {q : ℕ × ℕ}
    (hq : (segment x y x v).Contains q) :
    q.1 = x ∧ min y v ≤ q.2 ∧ q.2 ≤ max y v :=
  (vertical_mem x y v q).mp ((mem_pointHoles [segment x y x v] q).mpr
    ⟨segment x y x v, List.mem_singleton_self _, hq⟩)

private theorem horizontal_coordinates {x u y : ℕ} {q : ℕ × ℕ}
    (hq : (segment x y u y).Contains q) :
    q.2 = y ∧ min x u ≤ q.1 ∧ q.1 ≤ max x u :=
  (horizontal_mem x u y q).mp ((mem_pointHoles [segment x y u y] q).mpr
    ⟨segment x y u y, List.mem_singleton_self _, hq⟩)

private theorem point_coordinates {x y : ℕ} {q : ℕ × ℕ}
    (hq : (point x y).Contains q) : q.1 = x ∧ q.2 = y := by
  simp only [point, segment, Segment.Contains, Nat.min_self, Nat.max_self, true_and] at hq
  omega

private theorem endpoint_fixed_no_contact (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (e : Endpoint) (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels)
    {q : ℕ × ℕ} (hfixed : q ∈ pointHoles (endpointFixedSegments l (coordinates p) e))
    (hsignal : q ∈ pointHoles (endpointSegments (coordinates p) state e)) : False := by
  have hnear := endpoint_near p state e hsignal
  have hx : (coordinates p).length e.level + 64 < (coordinates p).x e.port :=
    readLength_add_lt_x p e.port e.level
  have hL : 16384 ≤ (coordinates p).length e.level := readLength_ge p hj hm
  have hu : 16384 ≤ (coordinates p).depth e.level := readDepth_ge p hj hm
  have huH : (coordinates p).depth e.level + 64 < p.H := readDepth_add_lt_H p e.level
  obtain ⟨s, hs, hq⟩ := (mem_pointHoles _ q).mp hfixed
  dsimp only [endpointFixedSegments] at hs
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hs
  rcases hs with rfl | rfl | rfl | hs | hs
  · have hv := vertical_coordinates hq
    cases hd : e.inward <;> simp [hd] at hnear hv <;> omega
  · have hv := vertical_coordinates hq
    have hrow : q.2 = onSide (coordinates p) e.side ((coordinates p).depth e.level) := by
      rcases hnear.2 with he | he
      · cases hd : e.inward <;> simp [hd] at hv <;> omega
      · exact he
    rw [hrow] at hv
    have hb := row_between p e.side (by omega) (by omega) (by omega) hv.2.1 hv.2.2
    omega
  · have hh := horizontal_coordinates hq
    cases hd : e.inward <;> simp [hd] at hnear hh <;> omega
  · obtain ⟨v, _, hs⟩ := List.mem_flatMap.mp hs
    rcases List.mem_append.mp hs with hs | hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hpoint := point_coordinates hq
        cases hd : e.inward <;> simp [hd] at hnear hpoint <;> omega
      · cases hs
    · split at hs
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
        subst s
        have hpoint := point_coordinates hq
        have hrow : q.2 = onSide (coordinates p) e.side ((coordinates p).depth e.level) := by
          rcases hnear.2 with he | he
          · cases hd : e.inward <;> simp only [inward, hd,
              Bool.false_eq_true, ite_false, ite_true] at hpoint <;> omega
          · exact he
        have he := rows_injective p e.side (by omega) (by omega) (hrow.symm.trans hpoint.2)
        omega
      · cases hs
  · split at hs
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      have hstep : e.level < p.levels := by assumption
      have hnext : (coordinates p).depth (e.level + 1) + 64 < p.H :=
        readDepth_add_lt_H p (e.level + 1)
      have hgap := readDepth_interlevel_margin p hj hstep
      change 2 * p.b e.level + 6 <
        ((coordinates p).depth (e.level + 1) - (coordinates p).depth e.level) / 2 - 2 at hgap
      rcases hs with rfl | rfl
      · have hpoint := point_coordinates hq
        cases hd : e.inward <;> simp [hd] at hnear hpoint <;> omega
      · have hpoint := point_coordinates hq
        have hrow : q.2 = onSide (coordinates p) e.side ((coordinates p).depth e.level) := by
          rcases hnear.2 with he | he
          · cases hd : e.inward <;> simp [hd] at hpoint <;> omega
          · exact he
        have he := rows_injective p e.side (by omega) (by omega) (hrow.symm.trans hpoint.2)
        omega
    · cases hs

/-- An actual endpoint's fixed streets, branches and separators share no hole with its signals. -/
theorem endpointFixedSegments_disjoint (l : PortLayout) (p : Scales.Parameters)
    (state : SignalState) (e : Endpoint) (hj : 1 ≤ e.level) (hm : e.level ≤ p.levels) :
    Disjoint (pointHoles (endpointFixedSegments l (coordinates p) e))
      (pointHoles (endpointSegments (coordinates p) state e)) :=
  Finset.disjoint_left.mpr fun _ hf hs => endpoint_fixed_no_contact l p state e hj hm hf hs

end PushPuzzle.PushS.PortLayout
